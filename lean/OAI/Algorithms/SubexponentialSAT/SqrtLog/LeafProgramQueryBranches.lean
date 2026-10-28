import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCleanup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafMarkedProgramWideNative
import OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram

namespace OAI.Algorithms

/-! The physical high-mask copy, exhaustive branch loop, and paid per-query
reclamation. The residual specification supplies the numeric branch values;
the program sums them itself and retains only the resulting count word. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls

def cleanupBound (W : ℕ) : ℕ := 2*W+6+cleanupPorts.length*(2*W+3)

theorem eval_width {c : Code} {n : ℕ} {a b : Data} (he : Eval c n a b)
    (W : ℕ) (hw : ∀i,(a.stacks i).length ≤ W) :
    ∀i,(b.stacks i).length ≤ W+n := by
  intro i
  exact (Subexp.SequentialProgram.trace_stack_length_le (compiled_trace he i i) i).trans
    (Nat.add_le_add_right (hw i) n)

def branches (residual : Code) : Code := .seq (Marked.Wide.nativeQuery residual) cleanup

def branchBudget (a : Data) (B W : ℕ) : ℕ :=
  let K := 7*(a.stacks 338).length+5
  K+B+cleanupBound (W+K+B)

theorem branches_eval (residual : Code) (a : Data)
    (ready : (Fin 763 → List Bool) → Prop) (count B width W : ℕ)
    (ctx : Marked.Wide.BranchContext residual (Marked.Wide.maskCopied a) ready count B width)
    (htmp : a.stacks 339=[]) (hw : ∀i,(a.stacks i).length ≤ W) :
    ∃ n middle, n ≤ branchBudget a B W ∧ Eval (branches residual) n a (cleaned middle) ∧
      (cleaned middle).stacks 320=a.stacks 320 ∧
      (cleaned middle).stacks 322=a.stacks 322 ∧
      BinaryArithmetic.toNat ((cleaned middle).stacks 323)=count ∧
      ((cleaned middle).stacks 323).length ≤ width ∧
      (∀i,¬Protected i → (cleaned middle).stacks i=[]) ∧
      (cleaned middle).regs 16=false ∧ (cleaned middle).regs 17=true ∧
      (cleaned middle).regs 18=false ∧ ready (Marked.Wide.workspace middle) := by
  obtain ⟨nb,middle,hnb,hr,hs,ha,hv,hl,h321,h324,h16,h17,h18,he⟩ :=
    Marked.Wide.branchContext_eval residual (Marked.Wide.maskCopied a) ready count B width ctx
  have hc := Marked.Wide.maskCopy_eval a htmp
  have hn := hc.seq he
  have hwidth : ∀i,(middle.stacks i).length ≤ W+(7*(a.stacks 338).length+5)+B := by
    intro i
    have h := eval_width hn W hw i
    omega
  have hcost := cleanupCost_le middle _ hwidth
  refine ⟨(7*(a.stacks 338).length+5+nb)+cleanupCost middle,middle,?_,
    hn.seq (cleanup_eval middle),?_,?_,?_,?_,cleaned_empty middle,?_,?_,?_,hr⟩
  · change _ ≤ (7*(a.stacks 338).length+5)+B+
      cleanupBound (W+(7*(a.stacks 338).length+5)+B)
    change cleanupCost middle ≤ cleanupBound (W+(7*(a.stacks 338).length+5)+B) at hcost
    omega
  · rw [cleaned_frame middle 320 (by decide)]
    exact hs.trans (Marked.Wide.maskCopied_frame a 320 (by decide))
  · rw [cleaned_frame middle 322 (by decide)]
    exact ha.trans (Marked.Wide.maskCopied_frame a 322 (by decide))
  · rw [cleaned_frame middle 323 (by decide)]
    exact hv
  · rw [cleaned_frame middle 323 (by decide)]
    exact hl
  · rw [cleaned_register_frame middle 16 (by decide)]
    exact h16
  · rw [cleaned_register_frame middle 17 (by decide)]
    exact h17
  · rw [cleaned_register_frame middle 18 (by decide)]
    exact h18

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
