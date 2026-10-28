import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IdentityConormalLinear
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.GroupPointSubtraction

/-! # Translated Conormal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TranslatedConormal

noncomputable section

/-! At a complex point, the actual group-lift conormal comparison is
the composition of the native point-subtraction differential and the
linear identity-conormal comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver LieRanks.dualNumberTest PELModuli.IntegralModel.Section.ConormalMaps.SectionConormal.module

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom] [GrpObj X]
local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)

theorem constructedIdentityLiftConormalEquiv_native_inverse (v : ModelX)
    (c : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ X) :
    ((Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ X ℂ c).symm (IdentityConormalLinear.nativeIdentityConormalLinear X v)).val =
      (show EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ X from (SchemeDualTangent.nativeSchemeTangentDualEquiv X 1 v).val) * c :=
  IdentityConormalLinear.nativeIdentityConormalLinear_inverse X v c

theorem nativeTranslatedConormal_eq (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (v : ModelX)
    (c : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ X)
    (hc : c = (show EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ X from toUnit (LieRanks.dualNumberTest ℂ) ≫ p))
    (f : {f : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ X // Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ ℂ ≫ f = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ ℂ ≫ c})
    (hf : f.val = (show EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ X from (SchemeDualTangent.nativeSchemeTangentDualEquiv X p v).val)) :
    Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ X ℂ c f =
      IdentityConormalLinear.nativeIdentityConormalLinear X (GroupPointSubtraction.nativeGroupPointSubtraction X p v) := by
  apply (Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ X ℂ c).symm.injective
  apply Subtype.ext
  have hl := congrArg (fun z => z.val) ((Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ X ℂ c).symm_apply_apply f)
  have hr := constructedIdentityLiftConormalEquiv_native_inverse X (GroupPointSubtraction.nativeGroupPointSubtraction X p v) c
  have hs : (show EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ X from
      (SchemeDualTangent.nativeSchemeTangentDualEquiv X 1 (GroupPointSubtraction.nativeGroupPointSubtraction X p v)).val) =
      (show EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ X from (SchemeDualTangent.nativeSchemeTangentDualEquiv X p v).val) /
        (show EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ X from toUnit (LieRanks.dualNumberTest ℂ) ≫ p) :=
    GroupPointSubtraction.nativeSchemeTangentDual_subtract X p v
  have he : (show EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ X from
      (SchemeDualTangent.nativeSchemeTangentDualEquiv X 1 (GroupPointSubtraction.nativeGroupPointSubtraction X p v)).val) * c =
      (show EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber ℂ) ⟶ X from (SchemeDualTangent.nativeSchemeTangentDualEquiv X p v).val) := by
    rw [hc, hs]
    exact div_mul_cancel _ _
  exact hl.trans (hf.trans (hr.trans he).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TranslatedConormal
