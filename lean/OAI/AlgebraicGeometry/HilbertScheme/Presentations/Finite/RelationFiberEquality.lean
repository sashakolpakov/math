import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ResidueFieldDetection
import Mathlib.RingTheory.Flat.Equalizer

/-! # Relation Fiber Equality -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.RelationFiberEquality

noncomputable section

/-! Residue-field detection for nested submodules with finite upper
relation module and flat upper quotient, over arbitrary coefficient rings. -/

open TensorProduct

universe u v
variable (R : Type u) [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

theorem finite_relation_eq_of_residue_baseChange (p q : Submodule R M) (hpq : p ≤ q)
    [Module.Finite R q] [Module.Flat R (M ⧸ q)]
    (h : ∀ r : PrimeSpectrum R, p.baseChange r.asIdeal.ResidueField = q.baseChange r.asIdeal.ResidueField) :
    p = q := by
  have hsurj : Function.Surjective (Submodule.inclusion hpq) := by
    apply ResidueFieldDetection.surjective_of_residueFields_of_finite_cokernel R (Submodule.inclusion hpq)
    intro r y
    let K := r.asIdeal.ResidueField
    have hy : q.subtype.lTensor K y ∈ p.baseChange K := by
      rw [h r]
      exact (q.toBaseChange K y).property
    obtain ⟨x, hx⟩ := p.toBaseChange_surjective' K hy
    refine ⟨x, ?_⟩
    apply LinearMap.lTensor_injective_of_exact_of_flat q.mkQ q.mkQ_surjective q.subtype
      q.subtype_injective (LinearMap.exact_subtype_mkQ q) K
    have he : q.subtype.comp (Submodule.inclusion hpq) = p.subtype := rfl
    rw [← LinearMap.lTensor_comp_apply, he]
    exact hx
  apply le_antisymm hpq
  intro x hx
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  have he : y.val = x := congrArg Subtype.val hy
  exact he ▸ y.property

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.RelationFiberEquality
