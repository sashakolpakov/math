import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRankProvenance
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeadsScope
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingConcrete

namespace OAI.Algorithms

/-! The native packing's coverage follows from the energy of the actual
conditional-expectation assignment, with no independent quality witness. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open PackingCallerProgram LayoutProducedHeads

 theorem words_eq_assignment (p : Problem) (a : Word p.r p.Q)
    (tail : List (Word p.r p.Q)) (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) :
    words p a tail=problemAssignment p a tail := by
  funext v
  have he := congrFun (PackingProgram.selectedValues_eq_computedWords
    (owner p) (factor p) a tail
    (PackingProgram.Assembly.Scope.terms p.scopes p.n p.mask p.Q)
    (PackingIncidenceInput.Semantics.seedIndices p.n p.factors)
    (problemWeights p a tail) (problemX p) ((p.n:ℚ)/(2*(p.r:ℚ)))
    (problem_weight_incidence p a tail) (problem_weight_head p a tail haN haC)) v
  cases v with
  | inl v =>
    have hi : LocalExpectation.indexCode
        (PackingIncidenceInput.Semantics.seedIndices p.n p.factors) (.inl v)=v.val :=
      LeafHeadSetupProgram.source_head_index v
    rw [hi,SubexponentialSAT.Subexp.AssignmentEnumeration.decode_eq_reverse_getD] at he
    change (p.words a tail).getD v.val a=problemAssignment p a tail (.inl v) at he
    rw [List.getD_eq_getElem _ _ (by rw [p.words_length]; omega)] at he
    simpa only [words,List.get_eq_getElem] using he
  | inr f =>
    have hi : LocalExpectation.indexCode
        (PackingIncidenceInput.Semantics.seedIndices p.n p.factors) (.inr f)=p.n+f.val :=
      LeafHeadFactorsProgram.factor_index p.n p.factors f
    rw [hi,SubexponentialSAT.Subexp.AssignmentEnumeration.decode_eq_reverse_getD] at he
    change (p.words a tail).getD (p.n+f.val) a=problemAssignment p a tail (.inr f) at he
    rw [List.getD_eq_getElem _ _ (by rw [p.words_length]; omega)] at he
    simpa only [words,List.get_eq_getElem] using he

 theorem packing_coverage (p : Problem) (a : Word p.r p.Q)
    (tail : List (Word p.r p.Q)) (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail)
    (B b : ℕ)
    (hB : ∀ v,(Finset.univ.filter fun i => owner p i=v).card ≤ B)
    (hb : ∀ e,(Finset.univ.filter fun i => factor p i=e).card ≤ b)
    (hM : 0 < p.incidences) (hn : 0 < p.n)
    (hlarge : 4*(B+b)*(p.r^(2*p.Q))^2*p.s^2 ≤ p.incidences)
    (hhead : 16*p.Q*p.r^2 ≤ p.n) :
    (1-1/(p.s:ℚ))*(p.incidences:ℚ) ≤
      (packing p a tail).blockCount*(Fintype.card (UniversalType p.r p.Q 1):ℚ) := by
  let : NeZero p.r := ⟨Nat.ne_of_gt p.hr⟩
  have he := (problem_computed_energies p a tail haN haC B b hB hb hM hn hlarge hhead).1
  have henergy : Packing.energy (packing p a tail).label ≤
      ((1/(p.s:ℚ))*(Fintype.card (Fin p.incidences):ℚ)/
        (Fintype.card (UniversalType p.r p.Q 1):ℚ))^2 := by
    rw [packing_label,words_eq_assignment p a tail haN haC]
    simpa only [problemX,Fintype.card_fin,owner,factor] using he
  simpa only [Fintype.card_fin] using
    Packing.concrete_coverage_of_energy (packing p a tail) (1/(p.s:ℚ)) (by positivity) henergy

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms
