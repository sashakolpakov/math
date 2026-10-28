import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramDot

namespace OAI.Algorithms

/-! The complete measured coefficient scan for one integer signature row.
Runtime EOF controls the loop; no instruction count depends on row length. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.MatrixProgramSupport

def rowValue (W : List Bool) (coeffs : List (List Bool)) (bits : List Bool) : ℕ :=
  (List.zipWith (fun c b => if b then SubexponentialSAT.BinaryArithmetic.toNat c
    else SubexponentialSAT.BinaryArithmetic.toNat W) coeffs bits).sum

def rowWidth (W : List Bool) (coeffs : List (List Bool)) (acc : List Bool) : ℕ :=
  acc.length + coeffs.length*(W.length+1) + (coeffs.map List.length).sum

def rowBudget (W : List Bool) (coeffs : List (List Bool)) (acc : List Bool) : ℕ :=
  (coeffs.length+1)*(200*(rowWidth W coeffs acc+2)^2+34)

def dotPeek : DotCode := .base (.atom (.peek 9 0 1))
def dotBody : DotCode := .seq dotStep dotPeek
def dotLoop : DotCode := .while 1 dotBody
def rowCommand : DotCode := .seq dotPeek dotLoop
def rowProgram := compiled rowCommand 9 2

def rowReady (regs : Fin 8 → Bool) (W : List Bool) (coeffs : List (List Bool))
    (bits acc : List Bool) : DotData :=
  dotState (readRegs regs 0 1 (words coeffs).head?) W coeffs bits acc

theorem dotPeek_eval (regs : Fin 8 → Bool) (W : List Bool) (coeffs : List (List Bool))
    (bits acc : List Bool) :
    Eval dotPeek 1 (dotState regs W coeffs bits acc) (rowReady regs W coeffs bits acc) := by
  exact Eval.base (StructuredProgram.Eval.atom _ _)

theorem rowReady_nil (regs : Fin 8 → Bool) (W bits acc : List Bool) :
    (rowReady regs W [] bits acc).regs 1 = false := by
  simp [rowReady, dotState, words, readRegs]

theorem rowReady_cons (regs : Fin 8 → Bool) (W c : List Bool)
    (cs : List (List Bool)) (bits acc : List Bool) :
    (rowReady regs W (c::cs) bits acc).regs 1 = true := by
  cases c <;> simp [rowReady, dotState, words, readRegs, Encoding.frame]

theorem dotLoop_eval (regs : Fin 8 → Bool) (W : List Bool) (coeffs : List (List Bool))
    (bits acc : List Bool) (hlen : coeffs.length = bits.length) :
    ∃ t ≤ rowBudget W coeffs acc, ∃ rf out,
      Eval dotLoop t (rowReady regs W coeffs bits acc) (dotState rf W [] [] out) ∧
      SubexponentialSAT.BinaryArithmetic.toNat out = SubexponentialSAT.BinaryArithmetic.toNat acc + rowValue W coeffs bits ∧
      out.length ≤ rowWidth W coeffs acc := by
  induction coeffs generalizing regs bits acc with
  | nil =>
      have hb : bits=[] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst bits
      refine ⟨1, ?_, (rowReady regs W [] [] acc).regs, acc, ?_, ?_, ?_⟩
      · simp [rowBudget, rowWidth]
      · exact Eval.while_false (rowReady_nil regs W [] acc)
      · simp [rowValue]
      · simp [rowWidth]
  | cons c cs ih =>
      cases bits with
      | nil => simp at hlen
      | cons bit bits =>
          have htail : cs.length=bits.length := by simpa using hlen
          obtain ⟨ts, hts, rs, mid, hes, hvs, hls⟩ := dotStep_eval
            (rowReady regs W (c::cs) (bit::bits) acc).regs W c cs bit bits acc
          obtain ⟨tt, htt, rt, out, het, hvt, hlt⟩ := ih rs bits mid htail
          have hs : Eval dotStep ts (rowReady regs W (c::cs) (bit::bits) acc)
              (dotState rs W cs bits mid) := hes
          have hbody : Eval dotBody (ts+1)
              (rowReady regs W (c::cs) (bit::bits) acc) (rowReady rs W cs bits mid) :=
            hs.seq (dotPeek_eval rs W cs bits mid)
          have he := Eval.while_true (rowReady_cons regs W c cs (bit::bits) acc) hbody het
          have hwidth : rowWidth W cs mid ≤ rowWidth W (c::cs) acc := by
            simp only [rowWidth, List.length_cons, List.map_cons, List.sum_cons, Nat.add_mul, Nat.one_mul]
            omega
          have hstart : W.length+c.length+acc.length+2 ≤ rowWidth W (c::cs) acc+2 := by
            simp only [rowWidth, List.length_cons, List.map_cons, List.sum_cons, Nat.add_mul, Nat.one_mul]
            omega
          have hstep : ts ≤ 200*(rowWidth W (c::cs) acc+2)^2+30 :=
            hts.trans (Nat.add_le_add_right
              (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left hstart 2)) 30)
          have htailCost : tt ≤ (cs.length+1)*(200*(rowWidth W (c::cs) acc+2)^2+34) := by
            exact htt.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right
              (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left (Nat.add_le_add_right hwidth 2) 2)) 34))
          refine ⟨(ts+1)+tt+1, ?_, rt, out, he, ?_, hlt.trans hwidth⟩
          · simp only [rowBudget, List.length_cons]
            nlinarith
          · rw [hvt, hvs]
            simp only [rowValue, List.zipWith_cons_cons, List.sum_cons]
            omega

theorem rowCommand_eval (regs : Fin 8 → Bool) (W : List Bool) (coeffs : List (List Bool))
    (bits acc : List Bool) (hlen : coeffs.length=bits.length) :
    ∃ t ≤ rowBudget W coeffs acc+1, ∃ rf out,
      Eval rowCommand t (dotState regs W coeffs bits acc) (dotState rf W [] [] out) ∧
      SubexponentialSAT.BinaryArithmetic.toNat out = SubexponentialSAT.BinaryArithmetic.toNat acc+rowValue W coeffs bits ∧
      out.length ≤ rowWidth W coeffs acc := by
  obtain ⟨t,ht,rf,out,he,hv,hl⟩ := dotLoop_eval regs W coeffs bits acc hlen
  exact ⟨1+t, by omega, rf,out,(dotPeek_eval regs W coeffs bits acc).seq he,hv,hl⟩

theorem rowProgram_runsIn (regs : Fin 8 → Bool) (W : List Bool) (coeffs : List (List Bool))
    (bits acc : List Bool) (hlen : coeffs.length=bits.length) :
    ∃ rf out,
      RunsIn rowProgram (rowBudget W coeffs acc+2)
        ((dotState regs W coeffs bits acc).withPC (some rowProgram.entry))
        ((dotState rf W [] [] out).withPC none) ∧
      SubexponentialSAT.BinaryArithmetic.toNat out = SubexponentialSAT.BinaryArithmetic.toNat acc+rowValue W coeffs bits := by
  obtain ⟨t,ht,rf,out,he,hv,hl⟩ := rowCommand_eval regs W coeffs bits acc hlen
  exact ⟨rf,out,⟨t+1,by omega,compiled_halt_trace he 9 2⟩,hv⟩

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
