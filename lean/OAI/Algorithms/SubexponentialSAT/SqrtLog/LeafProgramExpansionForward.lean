import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramExpansion
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! The preserved source lookup returns forward frame contents. Reverse this
actual tape before invoking the raw-tuple assembler. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Expansion
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

abbrev reverseInput : Cmd 40 768 :=
  .call (StackRoutines.reverseProgram 154 358 359 0 1)
abbrev forwardCommand : Cmd 40 768 := .seq reverseInput command

def reversedInput (a : Data) : Data := afterReverse a 154 0 1

theorem reversedInput_frame (a : Data) (i : Fin 768) (hi : i ≠ 154) :
    (reversedInput a).stacks i = a.stacks i := by
  simp [reversedInput,afterReverse,StackRoutines.reverseStacks,hi]

private theorem scratch_ne_input (i : Fin 768) (hi : i ∈ scratch) : i ≠ 154 := by
  simp only [scratch,List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst i <;> decide

theorem forward_command_eval (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (terms : List (Fin clauses.length × ZMod 3))
    (hbound : 3*clauses.length ≤ 2^b) (a : Data)
    (hraw : a.stacks 154 = (HashInputProgram.Loop.rawInput b terms).reverse)
    (hsource : a.stacks 700 = Encoding.encodeList id clauses)
    (hwidth : (a.stacks 708).length = b)
    (hmodulus : BinaryArithmetic.toNat (a.stacks 707) = clauses.length)
    (hshape : (a.stacks 280).length = (d+1)*SubexpLiftRing.baseWidth 3 t)
    (houtput : a.stacks 64 = [])
    (hwork : ∀ i ∈ scratch, a.stacks i = [])
    (h358 : a.stacks 358 = []) (h359 : a.stacks 359 = []) :
    ∃ k rf, k ≤ 9*(a.stacks 154).length + 7 +
        HashInputProgram.Loop.uniformBudget t d b (a.stacks 707) clauses terms.length + 3 ∧
      Eval forwardCommand k a
        (finished (reversedInput a) rf (outputWord t d clauses terms)) := by
  let x := reversedInput a
  have hframe (i : Fin 768) (hi : i ≠ 154) : x.stacks i = a.stacks i :=
    reversedInput_frame a i hi
  have hr : x.stacks 154 = HashInputProgram.Loop.rawInput b terms := by
    simp [x,reversedInput,afterReverse,StackRoutines.reverseStacks,hraw]
  have hw : ∀ i ∈ scratch, x.stacks i = [] := by
    intro i hi
    have hn := scratch_ne_input i hi
    exact (hframe i hn).trans (hwork i hi)
  obtain ⟨k,rf,hk,he⟩ := command_eval t d ht b hb clauses terms hbound x hr
    ((hframe 700 (by decide)).trans hsource)
    (by simpa only [hframe 708 (by decide)] using hwidth)
    (by simpa only [hframe 707 (by decide)] using hmodulus)
    (by simpa only [hframe 280 (by decide)] using hshape)
    ((hframe 64 (by decide)).trans houtput) hw
  have hv := reverse_eval a 154 358 359 0 1
    (by decide) (by decide) (by decide) (by decide) h358 h359
  have hk' : k ≤ HashInputProgram.Loop.uniformBudget t d b (a.stacks 707)
      clauses terms.length + 3 := by
    simpa only [hframe 707 (by decide)] using hk
  refine ⟨9*(a.stacks 154).length+7+k,rf,by omega,?_⟩
  exact hv.seq he

end SubexponentialSAT.SqrtLog.LeafProgram.Expansion

end OAI.Algorithms
