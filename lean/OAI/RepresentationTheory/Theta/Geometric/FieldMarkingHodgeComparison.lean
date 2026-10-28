import OAI.RepresentationTheory.Theta.Geometric.FieldMarkingCoordinateChange
import OAI.RepresentationTheory.Theta.Geometric.MarkedPolarizationIsometry
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMTypeHodgeCriterion
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CompactHodgeParts

/-! # Field Marking Hodge Comparison -/

namespace OAI.RepresentationTheory.Theta.Geometric.FieldMarkingHodgeComparison

noncomputable section

/-! The exact active kernel, original polarization, and full prescribed
embedding ranks determine the complete rational Hodge comparison. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMTypeHodgeCriterion OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CompactHodgeParts.IntrinsicHermitianMarking

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

include hs hg hdegree in
theorem fieldMarkingPeriodComparison_isHodgeMap
    (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (hρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback x.left) (ρ.pullback x.left))
    (hσ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (B.pullback y.left) (σ.pullback y.left))
    (hp : ∀ v w, PolarizedCanonicalForm.familyPolarizationForm B y (mB v) (mB w) = PolarizedCanonicalForm.familyPolarizationForm A x (mA v) (mA w))
    (hk : (FieldMarkingKernelRank.fieldMarkingFirstProjection A ρ x s mA P hP).ker =
      (FieldMarkingKernelRank.fieldMarkingFirstProjection B σ y s mB P hP).ker)
    (hrA : ∀ i, AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (A.abelian.pullback x.left) (ρ.pullback x.left)
      ((P.embeddings i).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) (P.firstLieRank i))
    (hrB : ∀ i, AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (B.abelian.pullback y.left) (σ.pullback y.left)
      ((P.embeddings i).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) (P.firstLieRank i)) :
    AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap (AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (PolarizedCanonicalForm.polarizedFamilyPresentation A x).variety)
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (PolarizedCanonicalForm.polarizedFamilyPresentation B y).variety)
      (FieldMarkingCoordinateChange.fieldMarkingPeriodComparison A ρ x B σ y mA mB).toLinearMap := by
  rw [FieldMarkingCoordinateChange.fieldMarkingPeriodComparison_eq_marked A ρ x B σ y s hs hg hdegree mA mB]
  apply AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMTypeHodgeCriterion.NativeHermitianMarking.markedPeriodTransport_isHodgeMap_of_CMType (A.pullback x.left) (B.pullback y.left)
    (ρ.pullback x.left) (σ.pullback y.left) s hs hg hdegree hρ hσ
    P.imaginaryScalar hP.2.2.2.2.2.2.1
    (FieldMarkingCoordinateChange.fieldMarkingCoordinateChange A ρ x B σ y s hs hg hdegree mA mB) P.embeddings hP.1.2
  · exact MarkedPolarizationIsometry.markedPolarization_isometry_hermitian (A.pullback x.left) (B.pullback y.left)
      (ρ.pullback x.left) (σ.pullback y.left) s hs hg hdegree hρ hσ
      P.imaginaryScalar hP.2.2.2.2.2.2.1
      (FieldMarkingCoordinateChange.fieldMarkingCoordinateChange A ρ x B σ y s hs hg hdegree mA mB)
      (FieldMarkingCoordinateChange.fieldMarkingCoordinateChange_polarization A ρ x B σ y s hs hg hdegree mA mB hp)
  · intro i
    by_cases hi : i = P.distinguished
    · subst i
      exact FieldMarkingCoordinateChange.fieldMarkingCoordinateChange_positivePart A ρ x B σ y s hs hg hdegree mA mB P hP hk
    · apply AlgebraicGeometry.AbelianModuli.ReferenceFamily.CompactHodgeParts.IntrinsicHermitianMarking.nativePositivePart_map_of_extreme_ranks (A.pullback x.left) (ρ.pullback x.left)
        s hs hg hdegree (P.embeddings i) (B.pullback y.left) (σ.pullback y.left)
        (FieldMarkingCoordinateChange.fieldMarkingCoordinateChange A ρ x B σ y s hs hg hdegree mA mB)
        (r := P.firstLieRank i) ?_ (hrA i) (hrB i)
      unfold AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.firstLieRank
      rw [ite_eq_right hi]
      split <;> simp

end

end OAI.RepresentationTheory.Theta.Geometric.FieldMarkingHodgeComparison
