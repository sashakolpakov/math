import OAI.RepresentationTheory.Theta.Geometric.ProductPeriodTorus
import OAI.RepresentationTheory.Theta.Geometric.AlgebraicAction
import OAI.AlgebraicGeometry.Albanese.Construction.SegreClosed
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicProductMaps

/-! # Product Period -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.ProductPeriod

noncomputable section

/-! The product period comparison lands in the actual product of the
original abelian varieties, with the native complex-point manifold. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.Manifold ContDiff

local instance nativeProductPeriod_integral (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance nativeProductPeriod_smooth (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance nativeProductPeriod_tensorIntegral (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral (A.toOver ⊗ B.toOver).left :=
  (AlgebraicGeometry.Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety A.variety B.variety).property
local instance nativeProductPeriod_tensorSmooth (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth (A.toOver ⊗ B.toOver).hom :=
  (AlgebraicGeometry.Albanese.Construction.SegreClosed.tensorSmoothProjectivePresentation A.variety.presentation B.variety.presentation).smooth

def nativeProductPointsDiffeomorph (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver × AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver) ≃ₘ⟮
      (𝓘(ℂ, AlgebraicAction.AbelianModel A)).prod 𝓘(ℂ, AlgebraicAction.AbelianModel B), 𝓘(ℂ, AlgebraicAction.AbelianModel (AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct A B))⟯
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct A B).toOver where
  toEquiv :=
    { toFun p := lift p.1 p.2
      invFun p := (p ≫ fst A.toOver B.toOver, p ≫ snd A.toOver B.toOver)
      left_inv p := Prod.ext (lift_fst p.1 p.2) (lift_snd p.1 p.2)
      right_inv p := by
        apply CartesianMonoidalCategory.hom_ext
        · exact lift_fst _ _
        · exact lift_snd _ _ }
  contMDiff_toFun :=
    ((AlgebraicGeometry.HodgeConjecture.DegreeTwo.IntrinsicProductMaps.Constructions.contMDiff_product_map (𝟙 (A.toOver ⊗ B.toOver))).of_le le_top).congr
      (fun p => Category.comp_id (lift p.1 p.2))
  contMDiff_invFun := (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (fst A.toOver B.toOver) ∞).prodMk
    (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (snd A.toOver B.toOver) ∞)

def productPeriodDiffeomorph (Φ Ψ : Torus.Data.CM.ProjectivePeriodData) (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (d : Ψ.periodTorus ≃ₘ⟮𝓘(ℂ, Ψ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel B)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver) :
    (Φ.product Ψ).periodTorus ≃ₘ⟮𝓘(ℂ, (Φ.product Ψ).space),
      𝓘(ℂ, AlgebraicAction.AbelianModel (AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct A B))⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct A B).toOver := by
  let ed : (Φ.periodTorus × Ψ.periodTorus) ≃ₘ⟮(𝓘(ℂ, Φ.space)).prod 𝓘(ℂ, Ψ.space),
      (𝓘(ℂ, AlgebraicAction.AbelianModel A)).prod 𝓘(ℂ, AlgebraicAction.AbelianModel B)⟯
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver × AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver) :=
    { toEquiv := e.toEquiv.prodCongr d.toEquiv
      contMDiff_toFun := (e.contMDiff.comp contMDiff_fst).prodMk (d.contMDiff.comp contMDiff_snd)
      contMDiff_invFun := (e.symm.contMDiff.comp contMDiff_fst).prodMk (d.symm.contMDiff.comp contMDiff_snd) }
  exact ((Φ.productTorusDiffeomorph Ψ).trans ed).trans (nativeProductPointsDiffeomorph A B)

theorem productPeriodDiffeomorph_mk (Φ Ψ : Torus.Data.CM.ProjectivePeriodData) (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (d : Ψ.periodTorus ≃ₘ⟮𝓘(ℂ, Ψ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel B)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver)
    (u : Φ.space) (v : Ψ.space) :
    productPeriodDiffeomorph Φ Ψ A B e d (QuotientAddGroup.mk (u, v)) =
      lift (e (QuotientAddGroup.mk u)) (d (QuotientAddGroup.mk v)) := rfl

theorem nativeProductPoints_mul (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a a' : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver) (b b' : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver) :
    (lift (a * a') (b * b') : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AlgebraicGeometry.Albanese.Construction.SegreClosed.abelianProduct A B).toOver) =
      lift a b * lift a' b' := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [MonObj.mul_comp, lift_fst]
  · simp only [MonObj.mul_comp, lift_snd]

theorem productPeriodDiffeomorph_apply (Φ Ψ : Torus.Data.CM.ProjectivePeriodData) (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (d : Ψ.periodTorus ≃ₘ⟮𝓘(ℂ, Ψ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel B)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver)
    (t : (Φ.product Ψ).periodTorus) :
    productPeriodDiffeomorph Φ Ψ A B e d t =
      lift (e ((Φ.productTorusEquiv Ψ t).1)) (d ((Φ.productTorusEquiv Ψ t).2)) := rfl

theorem productPeriodDiffeomorph_add (Φ Ψ : Torus.Data.CM.ProjectivePeriodData) (A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : Φ.periodTorus ≃ₘ⟮𝓘(ℂ, Φ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel A)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)
    (d : Ψ.periodTorus ≃ₘ⟮𝓘(ℂ, Ψ.space), 𝓘(ℂ, AlgebraicAction.AbelianModel B)⟯ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver)
    (he : ∀ u v, e (u + v) = e u * e v) (hd : ∀ u v, d (u + v) = d u * d v)
    (u v : (Φ.product Ψ).periodTorus) :
    productPeriodDiffeomorph Φ Ψ A B e d (u + v) =
      productPeriodDiffeomorph Φ Ψ A B e d u * productPeriodDiffeomorph Φ Ψ A B e d v := by
  rw [productPeriodDiffeomorph_apply, productPeriodDiffeomorph_apply, productPeriodDiffeomorph_apply,
    map_add, Prod.fst_add, Prod.snd_add, he, hd]
  exact nativeProductPoints_mul A B _ _ _ _

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.ProductPeriod
