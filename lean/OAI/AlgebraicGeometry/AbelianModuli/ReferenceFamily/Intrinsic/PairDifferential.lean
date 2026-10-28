import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeDualNaturality
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicProductMaps

/-! # Pair Differential -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PairDifferential

noncomputable section

/-! The native differential of the genuine map pairing scheme points
has the expected projection components. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Manifold ContDiff

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase)

def nativePointPair (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (X ⊗ Y) := lift p.1 p.2

variable [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
    [IsIntegral (X ⊗ Y).left] [Smooth (X ⊗ Y).hom]

local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "ModelY" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)
local notation "ModelP" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Over.hom (X ⊗ Y))) → ℂ)

theorem nativePointPair_mdifferentiable :
    MDifferentiable ((𝓘(ℂ, ModelX)).prod (𝓘(ℂ, ModelY))) 𝓘(ℂ, ModelP) (nativePointPair X Y) := by
  have h := HodgeConjecture.DegreeTwo.IntrinsicProductMaps.Constructions.contMDiff_product_map (𝟙 (X ⊗ Y))
  have he : (fun p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y =>
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (𝟙 (X ⊗ Y)) (lift p.1 p.2)) = nativePointPair X Y := by
    funext p
    exact Category.comp_id _
  rw [he] at h
  exact (h.of_le (show (1 : ℕ∞ω) ≤ ω from le_top)).mdifferentiable one_ne_zero

theorem nativePointPair_derivative_fst (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
    (v : ModelX × ModelY) :
    mfderiv 𝓘(ℂ, ModelP) 𝓘(ℂ, ModelX) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (fst X Y))
      (nativePointPair X Y p)
      (mfderiv ((𝓘(ℂ, ModelX)).prod (𝓘(ℂ, ModelY))) 𝓘(ℂ, ModelP)
        (nativePointPair X Y) p v) = v.1 := by
  have hc := mfderiv_comp_apply (I := (𝓘(ℂ, ModelX)).prod (𝓘(ℂ, ModelY)))
    (I' := 𝓘(ℂ, ModelP)) (I'' := 𝓘(ℂ, ModelX)) p
    ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (fst X Y) 1).mdifferentiableAt one_ne_zero)
    (nativePointPair_mdifferentiable X Y p) v
  have he : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (fst X Y) ∘ nativePointPair X Y = Prod.fst := by
    funext z
    exact lift_fst z.1 z.2
  have hd := congrArg (fun f : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X =>
    mfderiv ((𝓘(ℂ, ModelX)).prod (𝓘(ℂ, ModelY))) 𝓘(ℂ, ModelX) f p v) he
  exact hc.symm.trans (hd.trans (by rw [mfderiv_fst]; rfl))

theorem nativePointPair_derivative_snd (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
    (v : ModelX × ModelY) :
    mfderiv 𝓘(ℂ, ModelP) 𝓘(ℂ, ModelY) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (snd X Y))
      (nativePointPair X Y p)
      (mfderiv ((𝓘(ℂ, ModelX)).prod (𝓘(ℂ, ModelY))) 𝓘(ℂ, ModelP)
        (nativePointPair X Y) p v) = v.2 := by
  have hc := mfderiv_comp_apply (I := (𝓘(ℂ, ModelX)).prod (𝓘(ℂ, ModelY)))
    (I' := 𝓘(ℂ, ModelP)) (I'' := 𝓘(ℂ, ModelY)) p
    ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (snd X Y) 1).mdifferentiableAt one_ne_zero)
    (nativePointPair_mdifferentiable X Y p) v
  have he : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (snd X Y) ∘ nativePointPair X Y = Prod.snd := by
    funext z
    exact lift_snd z.1 z.2
  have hd := congrArg (fun f : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y =>
    mfderiv ((𝓘(ℂ, ModelX)).prod (𝓘(ℂ, ModelY))) 𝓘(ℂ, ModelY) f p v) he
  exact hc.symm.trans (hd.trans (by rw [mfderiv_snd]; rfl))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PairDifferential
