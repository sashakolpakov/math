import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionPeriodPairing

/-! # Class Pairing Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ClassPairingNaturality

noncomputable section

/-! The pairing from an actual product line-bundle class is natural
in both algebraic factors, through their genuine singular homology maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

def nativeProductClassPairing (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (q : HilbertConstruction.Line.Bundles.LineBundle.IsoClass (A.toOver ⊗ B.toOver).left) :
    HomologyCrossPairing.firstHomology (Betti.Scheme.schemePointSpace A.toOver) →ₗ[ℚ] HomologyCrossPairing.firstHomology (Betti.Scheme.schemePointSpace B.toOver) →ₗ[ℚ] ℚ :=
  CrossClassEvaluation.crossClassPairing (Betti.Scheme.schemePointSpace A.toOver) (Betti.Scheme.schemePointSpace B.toOver)
    (Intrinsic.ProductCohomology.nativeProductCohomologyPullback A B
      (Intrinsic.ChernClasses.lineBundleClassChernClass (Albanese.Construction.SegreClosed.tensorSmoothProjectivePresentation A.variety.presentation B.variety.presentation) q))

theorem nativeProductClassPairing_pullback (A B A' B' : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : A.toOver ⟶ A'.toOver) (g : B.toOver ⟶ B'.toOver)
    (q : HilbertConstruction.Line.Bundles.LineBundle.IsoClass (A'.toOver ⊗ B'.toOver).left)
    (x : HomologyCrossPairing.firstHomology (Betti.Scheme.schemePointSpace A.toOver)) (y : HomologyCrossPairing.firstHomology (Betti.Scheme.schemePointSpace B.toOver)) :
    nativeProductClassPairing A B (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (f ⊗ₘ g).left q) x y =
      nativeProductClassPairing A' B' q
        (homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f))) 1 x)
        (homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous g))) 1 y) := by
  let X := Albanese.Construction.SegreClosed.tensorSmoothProjectivePresentation A.variety.presentation B.variety.presentation
  let Y := Albanese.Construction.SegreClosed.tensorSmoothProjectivePresentation A'.variety.presentation B'.variety.presentation
  let F := TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f)
  let G := TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous g)
  let p := AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((F, G) : (Betti.Scheme.schemePointSpace A.toOver, Betti.Scheme.schemePointSpace B.toOver) ⟶
    (Betti.Scheme.schemePointSpace A'.toOver, Betti.Scheme.schemePointSpace B'.toOver))
  let c := Intrinsic.ChernClasses.lineBundleClassChernClass Y q
  have hc := ChernClassOperations.lineBundleClassChernClass_pullback (X := Y) (Y := X) (f ⊗ₘ g) q
  have hs := Intrinsic.ProductCohomology.singularCohomology_commuting_square (Intrinsic.ProductPoints.nativeProductPointMap A B)
    (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous (f ⊗ₘ g))) p (Intrinsic.ProductPoints.nativeProductPointMap A' B')
    (Intrinsic.ProductPoints.nativeProductPointMap_naturality A B A' B' f g) 2 c
  have h := (congrArg (Intrinsic.ProductCohomology.nativeProductCohomologyPullback A B) hc).trans hs
  exact (congrArg (fun c => CrossClassEvaluation.crossClassPairing (Betti.Scheme.schemePointSpace A.toOver) (Betti.Scheme.schemePointSpace B.toOver) c x y) h).trans
    (CrossClassEvaluation.crossClassPairing_naturality F G (Intrinsic.ProductCohomology.nativeProductCohomologyPullback A' B' c) x y)

theorem nativePointHomology_id (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (x : HomologyCrossPairing.firstHomology (Betti.Scheme.schemePointSpace A.toOver)) :
    homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous (𝟙 A.toOver)))) 1 x = x := by
  have h : TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous (𝟙 A.toOver)) = 𝟙 (Betti.Scheme.schemePointSpace A.toOver) := by
    apply TopCat.ext
    intro p
    exact Category.comp_id p
  rw [h]
  exact ConcreteCategory.congr_hom
    ((congrArg (fun a => homologyMap a 1) ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map_id (Betti.Scheme.schemePointSpace A.toOver))).trans
      (homologyMap_id ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).obj (Betti.Scheme.schemePointSpace A.toOver)) 1)) x

theorem nativeProductClassPairing_adjoint (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (q : HilbertConstruction.Line.Bundles.LineBundle.IsoClass (A.toOver ⊗ A.toOver).left)
    (f g : A.toOver ⟶ A.toOver)
    (hq : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (f ⊗ₘ 𝟙 A.toOver).left q =
      HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 A.toOver ⊗ₘ g).left q)
    (x y : HomologyCrossPairing.firstHomology (Betti.Scheme.schemePointSpace A.toOver)) :
    nativeProductClassPairing A A q
        (homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f))) 1 x) y =
      nativeProductClassPairing A A q x
        (homologyMap ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous g))) 1 y) := by
  have h := congrArg (fun q => nativeProductClassPairing A A q x y) hq
  have hl := nativeProductClassPairing_pullback A A A A f (𝟙 A.toOver) q x y
  have hr := nativeProductClassPairing_pullback A A A A (𝟙 A.toOver) g q x y
  rw [nativePointHomology_id] at hl hr
  exact hl.symm.trans (h.trans hr)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ClassPairingNaturality
