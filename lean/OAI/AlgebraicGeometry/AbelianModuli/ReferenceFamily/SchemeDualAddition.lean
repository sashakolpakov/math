import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeDualProducts
import OAI.AlgebraicGeometry.Albanese.Construction.Smooth

/-! # Scheme Dual Addition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeDualAddition

noncomputable section

/-! At the identity of a smooth integral complex group scheme, native
tangent addition is the intrinsic multiplication of dual-number points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom] [MonObj X]
local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "ModelP" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Over.hom (X ⊗ X))) → ℂ)

theorem nativeMultiplication_derivative_one (u v : ModelX) :
    mfderiv ((𝓘(ℂ, ModelX)).prod (𝓘(ℂ, ModelX))) 𝓘(ℂ, ModelX)
      (fun p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X => p.1 * p.2)
      (1, 1) (u, v) = u + v := by
  have hf : MDifferentiableAt ((𝓘(ℂ, ModelX)).prod (𝓘(ℂ, ModelX))) 𝓘(ℂ, ModelX)
      (fun p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X => p.1 * p.2) (1, 1) :=
    ((HodgeConjecture.DegreeTwo.IntrinsicProductMaps.Constructions.contMDiff_product_map (MonObj.mul (X := X))).of_le
      (show (1 : ℕ∞ω) ≤ ω from le_top)).mdifferentiableAt one_ne_zero
  have hd := mfderiv_prod_eq_add_apply (v := (u, v)) hf
  have hl : (fun z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X => z * 1) = id := funext mul_one
  have hr : (fun z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X => 1 * z) = id := funext one_mul
  have hld : mfderiv 𝓘(ℂ, ModelX) 𝓘(ℂ, ModelX)
      (fun z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X => z * 1) 1 u = u := by
    rw [hl, mfderiv_id]
    rfl
  have hrd : mfderiv 𝓘(ℂ, ModelX) 𝓘(ℂ, ModelX)
      (fun z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X => 1 * z) 1 v = v := by
    rw [hr, mfderiv_id]
    rfl
  exact hd.trans (congrArg₂ (· + ·) hld hrd)

theorem nativeSchemeTangentDual_add (u v : ModelX) :
    (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X 1 (u + v)).val =
      (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X 1 u).val * (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X 1 v).val := by
  let : IsIntegral (X ⊗ X).left := Albanese.Construction.Smooth.smooth_tensor_integral X X
  let : Smooth (X ⊗ X).hom := by
    change Smooth (Limits.pullback.fst X.hom X.hom ≫ X.hom)
    infer_instance
  let p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X := (1, 1)
  let r : ModelP := mfderiv ((𝓘(ℂ, ModelX)).prod (𝓘(ℂ, ModelX))) 𝓘(ℂ, ModelP)
    (Intrinsic.PairDifferential.nativePointPair X X) p (u, v)
  have hc := mfderiv_comp_apply (I := (𝓘(ℂ, ModelX)).prod (𝓘(ℂ, ModelX)))
    (I' := 𝓘(ℂ, ModelP)) (I'' := 𝓘(ℂ, ModelX)) p
    ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (MonObj.mul (X := X)) 1).mdifferentiableAt one_ne_zero)
    (Intrinsic.PairDifferential.nativePointPair_mdifferentiable X X p) (u, v)
  have hd : mfderiv 𝓘(ℂ, ModelP) 𝓘(ℂ, ModelX) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (MonObj.mul (X := X)))
      (Intrinsic.PairDifferential.nativePointPair X X p) r = u + v :=
    hc.symm.trans (nativeMultiplication_derivative_one X u v)
  have hn := SchemeDualNaturality.nativeSchemeTangentDual_natural (MonObj.mul (X := X)) (Intrinsic.PairDifferential.nativePointPair X X p) r
  have hp : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (MonObj.mul (X := X)) (Intrinsic.PairDifferential.nativePointPair X X p) =
      (1 : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := one_mul 1
  have he := congrArg (fun q => (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X q
    (mfderiv 𝓘(ℂ, ModelP) 𝓘(ℂ, ModelX) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (MonObj.mul (X := X)))
      (Intrinsic.PairDifferential.nativePointPair X X p) r)).val) hp
  have hv := congrArg (fun w : ModelX => (Intrinsic.SchemeDualTangent.nativeSchemeTangentDualEquiv X 1 w).val) hd
  have ht := congrArg (fun f : LieRanks.dualNumberTest ℂ ⟶ X ⊗ X => f ≫ MonObj.mul (X := X))
    (SchemeDualProducts.nativeSchemeTangentDual_product X X p (u, v))
  exact hv.symm.trans (he.symm.trans (hn.trans ht))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SchemeDualAddition
