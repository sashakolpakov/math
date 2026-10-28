import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PairDifferential

/-! # Scheme Dual Products -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeDualProducts

noncomputable section

/-! Pairing genuine dual-number points agrees with the differential of
pairing native complex scheme points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Manifold ContDiff

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
    [IsIntegral (X ⊗ Y).left] [Smooth (X ⊗ Y).hom]

local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "ModelY" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)
local notation "ModelP" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Over.hom (X ⊗ Y))) → ℂ)

theorem nativeSchemeTangentDual_product (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
    (v : ModelX × ModelY) :
    (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv (X ⊗ Y) (Intrinsic.PairDifferential.nativePointPair X Y p)
      (mfderiv ((𝓘(ℂ, ModelX)).prod (𝓘(ℂ, ModelY))) 𝓘(ℂ, ModelP)
        (Intrinsic.PairDifferential.nativePointPair X Y) p v)).val =
      lift (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X p.1 v.1).val
        (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv Y p.2 v.2).val := by
  let r := mfderiv ((𝓘(ℂ, ModelX)).prod (𝓘(ℂ, ModelY))) 𝓘(ℂ, ModelP)
    (Intrinsic.PairDifferential.nativePointPair X Y) p v
  apply hom_ext
  · have hn := SchemeDualNaturality.nativeSchemeTangentDual_natural (fst X Y) (Intrinsic.PairDifferential.nativePointPair X Y p) r
    have hp : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (fst X Y) (Intrinsic.PairDifferential.nativePointPair X Y p) = p.1 :=
      lift_fst p.1 p.2
    have he := congrArg (fun q => (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X q
      (mfderiv 𝓘(ℂ, ModelP) 𝓘(ℂ, ModelX) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (fst X Y))
        (Intrinsic.PairDifferential.nativePointPair X Y p) r)).val) hp
    have hd := congrArg (fun w : ModelX => (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X p.1 w).val)
      (Intrinsic.PairDifferential.nativePointPair_derivative_fst X Y p v)
    exact hn.symm.trans (he.trans (hd.trans (lift_fst _ _).symm))
  · have hn := SchemeDualNaturality.nativeSchemeTangentDual_natural (snd X Y) (Intrinsic.PairDifferential.nativePointPair X Y p) r
    have hp : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (snd X Y) (Intrinsic.PairDifferential.nativePointPair X Y p) = p.2 :=
      lift_snd p.1 p.2
    have he := congrArg (fun q => (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv Y q
      (mfderiv 𝓘(ℂ, ModelP) 𝓘(ℂ, ModelY) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (snd X Y))
        (Intrinsic.PairDifferential.nativePointPair X Y p) r)).val) hp
    have hd := congrArg (fun w : ModelY => (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv Y p.2 w).val)
      (Intrinsic.PairDifferential.nativePointPair_derivative_snd X Y p v)
    exact hn.symm.trans (he.trans (hd.trans (lift_snd _ _).symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeDualProducts
