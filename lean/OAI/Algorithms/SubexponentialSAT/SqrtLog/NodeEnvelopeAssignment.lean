import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopeWords

namespace OAI.Algorithms

/-! The assignment setup and incidence staging preserve a fixed linear
storage cap. This estimate depends only on their explicit tape operations. -/
namespace SubexponentialSAT.SqrtLog.NodeEnvelope
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage MomentsAssembly MomentsProgram
open LeafProgram

theorem machine_bound (A : ℕ) (core : Product.Store) (high : Fin 768 → List Bool)
    (regs : Fin 40 → Bool) (hc : ∀ i,(Product.tapes core i).length ≤ A)
    (hh : WordCap A high) : WordCap A (machine regs core high).stacks := by
  intro i
  simp only [machine]
  split_ifs
  · exact hc _
  · exact hh i

theorem assignment_setup_bound (A : ℕ) (a : LeafAssignmentSetupProgram.Data)
    (rm rw : Fin 8 → Bool) (ha : WordCap A a.stacks) :
    WordCap A (LeafAssignmentSetupProgram.prepared a rm rw).stacks := by
  have hw : (LeafAssignmentSetupProgram.weight a).length ≤ A := by
    unfold LeafAssignmentSetupProgram.weight LeafWeightProgram.Native.result
    split_ifs <;> exact ha _
  rw [LeafAssignmentSetupProgram.prepared_stacks]
  apply WordCap.update _ _ _ hw
  apply WordCap.update _ _ _ (by simpa using ha 174)
  exact (((ha.update _ [] (by simp)).update _ [] (by simp)).update _ _ (ha 40)).update _ _ (ha 42)

theorem preparedAssignment_bound {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (degree : List Bool) (high : Fin 768 → List Bool) (A : ℕ)
    (hh : WordCap A high)
    (hc : ∀ i,(Product.tapes (emptyCore (FactorLoop.assignmentEnvironment q degree)) i).length ≤ A) :
    WordCap A (FactorLoop.preparedAssignment q degree high [] []) := by
  apply assignment_setup_bound
  apply machine_bound
  · simpa only [working_empty] using hc
  · exact hh

theorem copy_word_bound {S : ℕ} (src dst : Fin S) (a : SubexpSetupStorage.Data S)
    (B : ℕ) (ha : WordBound B a) : WordBound (2*B) (copyState src dst a) := by
  intro i
  rw [copyState_stack]
  by_cases hi : i=dst
  · subst i
    simp only [Function.update_same,List.length_append]
    have hs := ha src
    have hd := ha dst
    omega
  · rw [Function.update_of_ne hi]
    exact (ha i).trans (by omega)

theorem copies_word_bound {S : ℕ} (ps : List (Fin S × Fin S))
    (a : SubexpSetupStorage.Data S) (B : ℕ) (ha : WordBound B a) :
    WordBound (2^ps.length*B) (copyManyState ps a) := by
  induction ps generalizing a B with
  | nil => simpa [copyManyState] using ha
  | cons p ps ih =>
    have h := ih (copyState p.1 p.2 a) (2*B) (copy_word_bound _ _ _ _ ha)
    simpa only [copyManyState,List.length_cons,pow_succ,Nat.mul_assoc] using h

/-- All eighteen incidence copies and the unary cutoff increment, including
nonempty destinations, are paid by a fixed linear enlargement. -/
theorem incidence_staged_bound (a : Incidence.Data) (A : ℕ) (ha : WordBound A a) :
    WordBound (524288*A+1) (Incidence.staged a) := by
  have hb : WordBound (262144*A) (copyManyState Incidence.pairs a) := by
    have h := copies_word_bound Incidence.pairs a A ha
    norm_num [Incidence.pairs] at h
    exact h
  intro i
  by_cases hi : i=550
  · subst i
    have h138 := hb 138
    have h550 := hb 550
    simp only [Incidence.staged,SourceControls.cutoffState,Function.update_same,
      List.length_cons,List.length_append]
    omega
  · simp only [Incidence.staged,SourceControls.cutoffState,Function.update_of_ne hi]
    exact (hb i).trans (by omega)

end SubexponentialSAT.SqrtLog.NodeEnvelope

end OAI.Algorithms
