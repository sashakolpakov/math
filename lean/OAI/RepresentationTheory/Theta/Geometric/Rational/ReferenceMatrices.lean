import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.CentralPeriods
import OAI.RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding
import Mathlib.LinearAlgebra.Countable

/-! # Reference Matrices -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Countably many rational maps into a fixed central period marking
give holomorphic matrices on the actual family chart. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

attribute [local irreducible] PolarizedCanonicalForm.polarizedFamilyPresentation MarkingComplexTransport.markingComplexBasis

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left}
    {ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (H : Intrinsic.HolomorphicTransport.NativeHolomorphicTransport A ρ F)

abbrev Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.RationalReferenceLabel := NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E →ₗ[ℚ]
  AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))).variety

instance Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.rationalReferenceLabel_countable : Countable (Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.RationalReferenceLabel (E := E) (A := A) (C := C)) :=
  Finsupp.Countable.of_moduleFinite (R := ℚ)

variable {s : ℕ} (P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (t : Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.RationalReferenceLabel (E := E) (A := A) (C := C))

def Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.referenceMarkedCoefficients : Geometry.ComplexBall.PrescribedSignsB.Vec →L[ℂ] (Fin F.rank → ℂ) :=
  ((MarkingComplexTransport.markingComplexBasis H.centralMarking).equivFun.toLinearMap.comp
    ((t.baseChange ℂ).comp (Reference.FirstEmbedding.referenceFirstComplexInclusion P hP))).toContinuousLinearMap

def Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.referenceMarkedMatrix (z : Intrinsic.FamilyFrames.FamilyChartBase C) : Geometry.ComplexBall.PrescribedSignsB.Vec →L[ℂ] (Fin H.dimension → ℂ) :=
  (H.matrix z).comp (H.referenceMarkedCoefficients P hP t)

theorem Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.referenceMarkedMatrix_apply (z : Intrinsic.FamilyFrames.FamilyChartBase C) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    H.referenceMarkedMatrix P hP t z v = H.matrix z
      ((MarkingComplexTransport.markingComplexBasis H.centralMarking).equivFun
        (t.baseChange ℂ (Reference.FirstEmbedding.referenceFirstComplexInclusion P hP v))) := rfl

theorem Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.referenceMarkedMatrix_holomorphic :
    DifferentiableOn ℂ (H.referenceMarkedMatrix P hP t) H.compatible.neighborhood :=
  H.holomorphic.clm_comp (differentiableOn_const (H.referenceMarkedCoefficients P hP t))

attribute [local irreducible] Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.referenceMarkedMatrix Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.referenceMarkedCoefficients

theorem Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.referenceMarkedMatrix_kernel_iff (z : H.compatible.neighborhood) (v : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    H.referenceMarkedMatrix P hP t z v = 0 ↔
      (H.rationalTransport z).toLinearMap.baseChange ℂ
        (t.baseChange ℂ (Reference.FirstEmbedding.referenceFirstComplexInclusion P hP v)) ∈
          (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodProjection.IntrinsicRationalPeriods.complexPeriodProjection (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety).ker := by
  rw [H.referenceMarkedMatrix_apply, H.matrix_kernel_iff]

end

end OAI.RepresentationTheory.Theta.Geometric
