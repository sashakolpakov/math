import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CountableResidueFields
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Algebra.Hom.Rat

/-! # Coefficient Fields -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.CoefficientFields.Construction

noncomputable section

/-! Finite rational coefficients lie in an actual countable algebraically
closed subfield of the original geometric field. Such a subfield also
contains the image of every number field in the original field. -/

variable {k : Type} [Field k] [CharZero k] [IsAlgClosed k]

theorem countable_algebraicallyClosed_subfield_of_coefficients
    (R : Subalgebra ℚ k) [Countable R] :
    ∃ F : Subfield k, Countable F ∧ IsAlgClosed F ∧ ∀ r : R, (r : k) ∈ F := by
  let Q := FractionRing R
  let j : Q →+* k := IsFractionRing.lift (K := Q)
    (g := R.val.toRingHom) Subtype.val_injective
  let : Algebra Q k := j.toAlgebra
  let F := algebraicClosure Q k
  have : Countable Q := TateComparison.CountableResidueFields.countable_localization R Q (nonZeroDivisors R)
  have hcount : Countable F := Cardinal.mk_le_aleph0_iff.mp
    ((Algebra.IsAlgebraic.cardinalMk_le_max Q F).trans
      (max_le Cardinal.mk_le_aleph0 le_rfl))
  have hclosed : IsAlgClosed (algebraicClosure Q k) := IsAlgClosure.isAlgClosed Q
  refine ⟨F.toSubfield, hcount, hclosed, ?_⟩
  intro r
  have hj : algebraMap Q k (algebraMap R Q r) = (r : k) :=
    IsFractionRing.lift_algebraMap Subtype.val_injective r
  change (r : k) ∈ F
  rw [← hj]
  exact F.algebraMap_mem _

theorem finite_coefficients_in_countable_algebraicallyClosed_subfield (s : Finset k) :
    ∃ F : Subfield k, Countable F ∧ IsAlgClosed F ∧ (s : Set k) ⊆ F := by
  let R := Algebra.adjoin ℚ (s : Set k)
  have : Algebra.FiniteType ℚ R := Algebra.FiniteType.adjoin_of_finite s.finite_toSet
  have : Countable R := TateComparison.CountableResidueFields.countable_finiteType ℚ R
  obtain ⟨F, hF, ha, hRF⟩ := countable_algebraicallyClosed_subfield_of_coefficients R
  refine ⟨F, hF, ha, ?_⟩
  intro x hx
  exact hRF ⟨x, Algebra.subset_adjoin hx⟩

set_option backward.isDefEq.respectTransparency false in
theorem countable_subfield_finite_enlargement (F : Subfield k) [Countable F]
    (s : Finset k) :
    ∃ G : Subfield k, Countable G ∧ IsAlgClosed G ∧ F ≤ G ∧ (s : Set k) ⊆ G := by
  let R := Algebra.adjoin F (s : Set k)
  have : Algebra.FiniteType F R := Algebra.FiniteType.adjoin_of_finite s.finite_toSet
  have : Countable R := TateComparison.CountableResidueFields.countable_finiteType F R
  have : Countable (R.restrictScalars ℚ) := inferInstanceAs (Countable R)
  obtain ⟨G, hG, ha, hRG⟩ :=
    countable_algebraicallyClosed_subfield_of_coefficients (R.restrictScalars ℚ)
  change ∀ r : R, (r : k) ∈ G at hRG
  refine ⟨G, hG, ha, ?_, ?_⟩
  · intro x hx
    exact hRG (algebraMap F R ⟨x, hx⟩)
  · intro x hx
    exact hRG (⟨x, Algebra.subset_adjoin hx⟩ : R)

theorem algebraicallyClosed_subfield_contains_numberField
    (F : Subfield k) [IsAlgClosed F] {K : Type} [Field K] [NumberField K]
    (j : K →+* k) (x : K) : j x ∈ F := by
  have hx : IsAlgebraic ℚ (j x) :=
    (isAlgebraic_algHom_iff j.toRatAlgHom j.injective).mpr
      (Algebra.IsAlgebraic.isAlgebraic x)
  have hF : IsAlgebraic F (j x) := IsAlgebraic.tower_top (L := F) hx
  have hb : algebraicClosure F k = ⊥ :=
    (IsAlgClosed.algebraicClosure_eq_bot_iff F k).mpr inferInstance
  have hm : j x ∈ (⊥ : IntermediateField F k) :=
    hb ▸ (mem_algebraicClosure_iff.mpr hF)
  obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp hm
  exact hy ▸ y.property

def numberFieldToAlgebraicallyClosedSubfield
    (F : Subfield k) [IsAlgClosed F] {K : Type} [Field K] [NumberField K]
    (j : K →+* k) : K →+* F :=
  j.codRestrict F (algebraicallyClosed_subfield_contains_numberField F j)

theorem numberFieldToAlgebraicallyClosedSubfield_comp
    (F : Subfield k) [IsAlgClosed F] {K : Type} [Field K] [NumberField K]
    (j : K →+* k) :
    F.subtype.comp (numberFieldToAlgebraicallyClosedSubfield F j) = j := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Countable.CoefficientFields.Construction
