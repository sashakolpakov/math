import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT BitProgram StructuredCalls

/-- Semantic specification of the physically executed sequence of writes. -/
def scatter : List ℕ → List Bool → List Bool → List Bool
  | j::js, b::bs, mask => scatter js bs (write mask j b)
  | _, _, mask => mask

def scanCost : List ℕ → ℕ
  | [] => 1
  | j::js => 30*j+55+scanCost js

def peekBits : Code := .base (.atom (.peek 1 0 1))
def scanBody : Code := .seq scatterStep peekBits
def scanLoop : Code := .while 1 scanBody
def scanCommand : Code := .seq peekBits scanLoop

def ready (regs : Fin 8 → Bool) (saved : Fin 3 → List Bool)
    (js : List ℕ) (bits mask : List Bool) : Data :=
  state (readRegs regs 0 1 bits.head?) saved js bits mask

theorem peekBits_eval (regs : Fin 8 → Bool) (saved : Fin 3 → List Bool)
    (js : List ℕ) (bits mask : List Bool) :
    Eval peekBits 1 (state regs saved js bits mask) (ready regs saved js bits mask) := by
  exact Eval.base (StructuredProgram.Eval.atom _ _)

theorem scatter_length (js : List ℕ) (bits mask : List Bool)
    (hb : ∀ j ∈ js, j < mask.length) :
    (scatter js bits mask).length = mask.length := by
  induction js generalizing bits mask with
  | nil => rfl
  | cons j js ih =>
      cases bits with
      | nil => rfl
      | cons b bits =>
          have hj := hb j (by simp)
          have hw := write_length mask j b hj
          have ht : ∀ k ∈ js, k < (write mask j b).length := by
            intro k hk; rw [hw]; exact hb k (by simp [hk])
          exact (ih bits _ ht).trans hw

theorem scanLoop_eval (regs : Fin 8 → Bool) (saved : Fin 3 → List Bool)
    (js : List ℕ) (bits mask : List Bool)
    (hlen : js.length=bits.length) (hb : ∀ j ∈ js, j < mask.length) :
    ∃ rf, Eval scanLoop (scanCost js) (ready regs saved js bits mask)
      (state rf saved [] [] (scatter js bits mask)) := by
  induction js generalizing regs bits mask with
  | nil =>
      have he : bits=[] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst bits
      refine ⟨readRegs regs 0 1 none, ?_⟩
      exact Eval.while_false (by simp [ready,state,readRegs])
  | cons j js ih =>
      cases bits with
      | nil => simp at hlen
      | cons b bits =>
          have hj := hb j (by simp)
          obtain ⟨rs,hs⟩ := scatterStep_eval (readRegs regs 0 1 (some b)) saved
            j js b bits mask hj
          have hw := write_length mask j b hj
          obtain ⟨rf,hf⟩ := ih rs bits (write mask j b)
            (by simpa using hlen) (by intro k hk; rw [hw]; exact hb k (by simp [hk]))
          have hbody := hs.seq (peekBits_eval rs saved js bits (write mask j b))
          have he := Eval.while_true (show (ready regs saved (j::js) (b::bits) mask).regs 1=true
            by simp [ready,state,readRegs]) hbody hf
          refine ⟨rf, ?_⟩
          convert he using 1 <;> simp [scanLoop,scanBody,scanCost,scatter] ; omega

theorem scanCommand_eval (regs : Fin 8 → Bool) (saved : Fin 3 → List Bool)
    (js : List ℕ) (bits mask : List Bool)
    (hlen : js.length=bits.length) (hb : ∀ j ∈ js, j < mask.length) :
    ∃ rf, Eval scanCommand (scanCost js+1) (state regs saved js bits mask)
      (state rf saved [] [] (scatter js bits mask)) := by
  obtain ⟨rf,he⟩ := scanLoop_eval regs saved js bits mask hlen hb
  exact ⟨rf, by simpa [scanCommand,Nat.add_comm] using (peekBits_eval regs saved js bits mask).seq he⟩

theorem scanCost_bound (n : ℕ) (js : List ℕ) (hb : ∀ j ∈ js,j < n) :
    scanCost js ≤ js.length*(30*n+55)+1 := by
  induction js with
  | nil => simp [scanCost]
  | cons j js ih =>
      have hj := hb j (by simp)
      have ht := ih (by intro k hk; exact hb k (by simp [hk]))
      simp only [scanCost,List.length_cons]
      nlinarith

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
