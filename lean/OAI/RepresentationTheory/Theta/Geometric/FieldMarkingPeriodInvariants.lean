import OAI.RepresentationTheory.Theta.Geometric.FieldMarkingCoordinateChange

/-! # Field Marking Period Invariants -/

namespace OAI.RepresentationTheory.Theta.Geometric.FieldMarkingPeriodInvariants

noncomputable section

/-! The original lattice, rational polarization, and every integral
endomorphism are retained by the exact comparison of full field markings. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E]
    {S T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N T.left)
    (σ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian)
    (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints T)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (mA : let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ x
      NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A x).variety)
    (mB : let := CompatibleFieldEquiv.familyPeriodFieldModule B σ y
      NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation B y).variety)

theorem fieldMarkingPeriodComparison_integral
    (hi : ∀ v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, mA v ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A x).variety ↔
      mB v ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation B y).variety)
    (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A x).variety) :
    v ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A x).variety ↔
      FieldMarkingCoordinateChange.fieldMarkingPeriodComparison A ρ x B σ y mA mB v ∈
        AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation B y).variety := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ x
  obtain ⟨v₀, rfl⟩ := mA.surjective v
  rw [FieldMarkingCoordinateChange.fieldMarkingPeriodComparison_marking]
  exact hi v₀

theorem fieldMarkingPeriodComparison_polarization
    (hp : ∀ v w, PolarizedCanonicalForm.familyPolarizationForm B y (mB v) (mB w) = PolarizedCanonicalForm.familyPolarizationForm A x (mA v) (mA w))
    (v w : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A x).variety) :
    PolarizedCanonicalForm.familyPolarizationForm B y (FieldMarkingCoordinateChange.fieldMarkingPeriodComparison A ρ x B σ y mA mB v)
      (FieldMarkingCoordinateChange.fieldMarkingPeriodComparison A ρ x B σ y mA mB w) = PolarizedCanonicalForm.familyPolarizationForm A x v w := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ x
  obtain ⟨v₀, rfl⟩ := mA.surjective v
  obtain ⟨w₀, rfl⟩ := mA.surjective w
  rw [FieldMarkingCoordinateChange.fieldMarkingPeriodComparison_marking, FieldMarkingCoordinateChange.fieldMarkingPeriodComparison_marking]
  exact hp v₀ w₀

theorem fieldMarkingPeriodComparison_field (a : E)
    (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A x).variety) :
    FieldMarkingCoordinateChange.fieldMarkingPeriodComparison A ρ x B σ y mA mB (Family.FieldActions.familyFieldPeriodAction A ρ x a v) =
      Family.FieldActions.familyFieldPeriodAction B σ y a (FieldMarkingCoordinateChange.fieldMarkingPeriodComparison A ρ x B σ y mA mB v) := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ x
  let := CompatibleFieldEquiv.familyPeriodFieldModule B σ y
  exact (mA.symm.trans mB).map_smul a v

theorem fieldMarkingPeriodComparison_integer (a : NumberField.RingOfIntegers E)
    (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A x).variety) :
    FieldMarkingCoordinateChange.fieldMarkingPeriodComparison A ρ x B σ y mA mB (Family.FieldActions.familyIntegralPeriodAction A ρ x a v) =
      Family.FieldActions.familyIntegralPeriodAction B σ y a (FieldMarkingCoordinateChange.fieldMarkingPeriodComparison A ρ x B σ y mA mB v) := by
  rw [← Family.FieldActions.familyFieldPeriodAction_integer, ← Family.FieldActions.familyFieldPeriodAction_integer]
  exact fieldMarkingPeriodComparison_field A ρ x B σ y mA mB a v

end

end OAI.RepresentationTheory.Theta.Geometric.FieldMarkingPeriodInvariants
