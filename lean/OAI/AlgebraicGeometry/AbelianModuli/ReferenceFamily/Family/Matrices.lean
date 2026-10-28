import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CentralPeriods
import OAI.RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding
import Mathlib.LinearAlgebra.Countable

/-! # Matrices -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Countably many rational maps into a fixed central period marking
give holomorphic matrices on the actual family chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

open OAI.RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding

attribute [local irreducible] RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation Family.MarkingCoordinates.markingComplexBasis

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    {A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left}
    {ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian}
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (H : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport A ρ F)

abbrev Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.RationalReferenceLabel := NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →ₗ[ℚ]
  Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C))).variety

instance Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.rationalReferenceLabel_countable : Countable (Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.RationalReferenceLabel (E := E) (A := A) (C := C)) :=
  Finsupp.Countable.of_moduleFinite (R := ℚ)

variable {s : ℕ} (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (t : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.RationalReferenceLabel (E := E) (A := A) (C := C))

def Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.referenceMarkedCoefficients : Geometry.ComplexBall.PrescribedSignsB.Vec →L[ℂ] (Fin F.rank → ℂ) :=
  ((Family.MarkingCoordinates.markingComplexBasis H.centralMarking).equivFun.toLinearMap.comp
    ((t.baseChange ℂ).comp (RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding.referenceFirstComplexInclusion P hP))).toContinuousLinearMap

def Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.referenceMarkedMatrix (z : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C) : Geometry.ComplexBall.PrescribedSignsB.Vec →L[ℂ] (Fin H.dimension → ℂ) :=
  (H.matrix z).comp (H.referenceMarkedCoefficients P hP t)

theorem Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.referenceMarkedMatrix_apply (z : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    H.referenceMarkedMatrix P hP t z v = H.matrix z
      ((Family.MarkingCoordinates.markingComplexBasis H.centralMarking).equivFun
        (t.baseChange ℂ (RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding.referenceFirstComplexInclusion P hP v))) := rfl

theorem Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.referenceMarkedMatrix_holomorphic :
    DifferentiableOn ℂ (H.referenceMarkedMatrix P hP t) H.compatible.neighborhood :=
  H.holomorphic.clm_comp (differentiableOn_const (H.referenceMarkedCoefficients P hP t))

attribute [local irreducible] Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.referenceMarkedMatrix Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.referenceMarkedCoefficients

theorem Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.referenceMarkedMatrix_kernel_iff (z : H.compatible.neighborhood) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    H.referenceMarkedMatrix P hP t z v = 0 ↔
      (H.rationalTransport z).toLinearMap.baseChange ℂ
        (t.baseChange ℂ (RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding.referenceFirstComplexInclusion P hP v)) ∈
          (Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety).ker := by
  rw [H.referenceMarkedMatrix_apply, H.matrix_kernel_iff]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
