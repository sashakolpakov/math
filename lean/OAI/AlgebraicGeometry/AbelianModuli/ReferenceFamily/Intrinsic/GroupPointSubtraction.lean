import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupPointNormalization
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeDualNaturality

/-! # Group Point Subtraction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.GroupPointSubtraction

noncomputable section

/-! The actual native differential of point subtraction is a complex
linear map, and its dual-number realization is literal subtraction of
the fixed point from the original infinitesimal lift. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom] [GrpObj X]
local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)

def nativeGroupPointSubtraction (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) : ModelX →ₗ[ℂ] ModelX :=
  (mfderiv 𝓘(ℂ, ModelX) 𝓘(ℂ, ModelX) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (GroupPointNormalization.groupPointSubtract p)) p).toLinearMap

theorem nativeSchemeTangentDual_subtract (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (v : ModelX) :
    (SchemeDualTangent.nativeSchemeTangentDualEquiv X 1 (nativeGroupPointSubtraction X p v)).val =
      (SchemeDualTangent.nativeSchemeTangentDualEquiv X p v).val / (toUnit (LieRanks.dualNumberTest ℂ) ≫ p) := by
  have hp : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (GroupPointNormalization.groupPointSubtract p) p = (1 : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
    GroupPointNormalization.groupPointSubtract_point p
  have hn := SchemeDualNaturality.nativeSchemeTangentDual_natural (GroupPointNormalization.groupPointSubtract p) p v
  have he := congrArg (fun q => (SchemeDualTangent.nativeSchemeTangentDualEquiv X q (nativeGroupPointSubtraction X p v)).val) hp
  exact he.symm.trans (hn.trans (GroupPointNormalization.groupPointSubtract_comp p (SchemeDualTangent.nativeSchemeTangentDualEquiv X p v).val))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.GroupPointSubtraction
