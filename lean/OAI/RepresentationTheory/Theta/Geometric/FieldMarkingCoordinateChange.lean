import OAI.RepresentationTheory.Theta.Geometric.EmbeddedNormalizedTransport
import OAI.RepresentationTheory.Theta.Geometric.FieldMarkingPolarization
import OAI.RepresentationTheory.Theta.Geometric.FieldMarkingKernelRank
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.PeriodTransport

/-! # Field Marking Coordinate Change -/

namespace OAI.RepresentationTheory.Theta.Geometric.FieldMarkingCoordinateChange

noncomputable section

section

/-! Two full field markings with the same active kernel and original
polarization determine their exact native coordinate comparison. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
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

def fieldMarkingCoordinateChange : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E :=
  (FieldMarkingComplexCoordinates.fieldMarkingCoordinates A ρ x s hs hg hdegree mA).symm.trans
    (FieldMarkingComplexCoordinates.fieldMarkingCoordinates B σ y s hs hg hdegree mB)

omit [NumberField.IsCMField E] in
theorem fieldMarkingCoordinateChange_apply (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    fieldMarkingCoordinateChange A ρ x B σ y s hs hg hdegree mA mB
      (FieldMarkingComplexCoordinates.fieldMarkingCoordinates A ρ x s hs hg hdegree mA v) =
        FieldMarkingComplexCoordinates.fieldMarkingCoordinates B σ y s hs hg hdegree mB v :=
  congrArg (FieldMarkingComplexCoordinates.fieldMarkingCoordinates B σ y s hs hg hdegree mB)
    ((FieldMarkingComplexCoordinates.fieldMarkingCoordinates A ρ x s hs hg hdegree mA).symm_apply_apply v)

theorem fieldMarkingCoordinateChange_positivePart (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (hk : (FieldMarkingKernelRank.fieldMarkingFirstProjection A ρ x s mA P hP).ker =
      (FieldMarkingKernelRank.fieldMarkingFirstProjection B σ y s mB P hP).ker) :
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart (A.pullback x.left) (ρ.pullback x.left) s hs hg hdegree
      (P.embeddings P.distinguished)).map
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup.embeddedLinearIso (fieldMarkingCoordinateChange A ρ x B σ y s hs hg hdegree mA mB)
          (P.embeddings P.distinguished)).toLinearMap =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart (B.pullback y.left) (σ.pullback y.left) s hs hg hdegree
        (P.embeddings P.distinguished) := by
  apply EmbeddedNormalizedTransport.embeddedNormalizedSubmodule_transport
  exact ((FieldMarkingKernelRank.fieldMarkingFirstProjection_kernel A ρ x s hs hg hdegree mA P hP).symm.trans hk).trans
    (FieldMarkingKernelRank.fieldMarkingFirstProjection_kernel B σ y s hs hg hdegree mB P hP)

omit [NumberField.IsCMField E] in
theorem fieldMarkingCoordinateChange_polarization
    (hp : ∀ v w, PolarizedCanonicalForm.familyPolarizationForm B y (mB v) (mB w) = PolarizedCanonicalForm.familyPolarizationForm A x (mA v) (mA w))
    (v w : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm (B.pullback y.left) (σ.pullback y.left) s hs hg hdegree
      (fieldMarkingCoordinateChange A ρ x B σ y s hs hg hdegree mA mB v)
      (fieldMarkingCoordinateChange A ρ x B σ y s hs hg hdegree mA mB w) =
        AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedPolarizationForm (A.pullback x.left) (ρ.pullback x.left) s hs hg hdegree v w := by
  obtain ⟨v₀, rfl⟩ := (FieldMarkingComplexCoordinates.fieldMarkingCoordinates A ρ x s hs hg hdegree mA).surjective v
  obtain ⟨w₀, rfl⟩ := (FieldMarkingComplexCoordinates.fieldMarkingCoordinates A ρ x s hs hg hdegree mA).surjective w
  rw [fieldMarkingCoordinateChange_apply, fieldMarkingCoordinateChange_apply,
    ← Family.MarkedPolarization.familyMarkedPolarizationForm_original, ← Family.MarkedPolarization.familyMarkedPolarizationForm_original,
    FieldMarkingPolarization.fieldMarkingCoordinates_polarization, FieldMarkingPolarization.fieldMarkingCoordinates_polarization]
  exact hp v₀ w₀

end

/-! The comparison between two actual field markings agrees exactly
with the original marked rational period transport. -/

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

def fieldMarkingPeriodComparison :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A x).variety ≃ₗ[ℚ]
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation B y).variety := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ x
  let := Family.PELCoordinates.familyPeriodScalarTower A ρ x
  let := CompatibleFieldEquiv.familyPeriodFieldModule B σ y
  let := Family.PELCoordinates.familyPeriodScalarTower B σ y
  exact (mA.restrictScalars ℚ).symm.trans (mB.restrictScalars ℚ)

theorem fieldMarkingPeriodComparison_marking (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    fieldMarkingPeriodComparison A ρ x B σ y mA mB (mA v) = mB v := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ x
  let := CompatibleFieldEquiv.familyPeriodFieldModule B σ y
  exact congrArg mB (mA.symm_apply_apply v)

theorem fieldMarkingPeriodComparison_eq_marked :
    fieldMarkingPeriodComparison A ρ x B σ y mA mB =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport (A.abelian.pullback x.left)
        (B.abelian.pullback y.left) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (A.pullback x.left))
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (B.pullback y.left))
        (ρ.pullback x.left) (σ.pullback y.left) s hs hg hdegree
        (fieldMarkingCoordinateChange A ρ x B σ y s hs hg hdegree mA mB) := by
  let := CompatibleFieldEquiv.familyPeriodFieldModule A ρ x
  let := CompatibleFieldEquiv.familyPeriodFieldModule B σ y
  apply LinearEquiv.ext
  intro v
  obtain ⟨v₀, rfl⟩ := mA.surjective v
  rw [fieldMarkingPeriodComparison_marking]
  apply (Family.PELCoordinates.familyPELCoordinates B σ y s hs hg hdegree).injective
  exact (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Marked.PeriodTransport.IntrinsicPELMarking.markedPeriodTransport_coordinates
    (A.abelian.pullback x.left) (B.abelian.pullback y.left)
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (A.pullback x.left))
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.Projectivity.polarizedNativeProjectivePresentation (B.pullback y.left))
    (ρ.pullback x.left) (σ.pullback y.left) s hs hg hdegree
    (fieldMarkingCoordinateChange A ρ x B σ y s hs hg hdegree mA mB) (mA v₀)).trans
      (fieldMarkingCoordinateChange_apply A ρ x B σ y s hs hg hdegree mA mB v₀) |>.symm

end

end OAI.RepresentationTheory.Theta.Geometric.FieldMarkingCoordinateChange
