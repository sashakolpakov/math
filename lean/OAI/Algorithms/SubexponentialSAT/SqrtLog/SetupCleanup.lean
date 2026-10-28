import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SetupParameter
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Setup.Cleanup

open BitProgram StructuredCalls

abbrev Data (S : ℕ) := StructuredProgram.State 8 S

def clearMany {S : ℕ} : List (Fin S) → Cmd 8 S
  | [] => .base .skip
  | i::is => .seq (ArithmeticExpressionSupport.clearCmd i) (clearMany is)

theorem clearMany_eval {S : ℕ} (ports : List (Fin S)) (d : Data S) (B : ℕ)
    (hb : ∀ i, (d.stacks i).length ≤ B) :
    ∃ t e, Eval (clearMany ports) t d e ∧
      (∀ i, e.stacks i = if i ∈ ports then [] else d.stacks i) ∧
      t ≤ ports.length*(2*B+3) := by
  induction ports generalizing d with
  | nil => exact ⟨0,d,.base (.skip _),by simp,by simp⟩
  | cons p ps ih =>
    let a : Data S := ⟨readRegs d.regs 0 1 none,Function.update d.stacks p []⟩
    have h1 : Eval (ArithmeticExpressionSupport.clearCmd p) (2*(d.stacks p).length+3) d a :=
      ArithmeticExpressionSupport.clear_eval p d
    have ha : ∀ i, (a.stacks i).length ≤ B := by
      intro i; by_cases hi : i=p
      · subst i; simp [a]
      · simpa [a,hi] using hb i
    obtain ⟨t,e,he,hs,ht⟩ := ih a ha
    refine ⟨_,e,h1.seq he,?_,?_⟩
    · intro i
      rw [hs]
      by_cases hip : i=p
      · subst i; by_cases his : p∈ps <;> simp [his,a]
      · by_cases his : i∈ps <;> simp [hip,his,a]
    · have hp := hb p
      simp only [List.length_cons]
      nlinarith

/-- Generic trace space accounting: physically clearing a callee's output is
polynomial in the actual execution length even for padded zero words. -/
theorem output_length_le {S : ℕ} (c : Cmd 8 S) (input output : Fin S)
    {t : ℕ} {a b : Data S} (he : Eval c t a b) (i : Fin S) :
    (b.stacks i).length ≤ BitProgram.stackBits a.stacks + t + 1 := by
  have hs := BitProgram.trace_dataBits (compiled c input output)
    (compiled_halt_trace he input output)
  have hi : (b.stacks i).length ≤ BitProgram.stackBits b.stacks :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (b.stacks j).length) (Finset.mem_univ i)
  change BitProgram.stackBits b.stacks ≤ BitProgram.stackBits a.stacks + (t+1) at hs
  omega

end SubexponentialSAT.SqrtLog.Setup.Cleanup

end OAI.Algorithms
