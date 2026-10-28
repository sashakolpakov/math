import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BiextensionChernIdentity

/-! # Product Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProductPoints

noncomputable section

/-! Pairing native complex points is a continuous map to the actual
scheme product, with literal projection, multiplication and map laws. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

def nativeProductPointMap (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    TopCat.of (Betti.Scheme.schemePointSpace A.toOver × Betti.Scheme.schemePointSpace B.toOver) ⟶
      Betti.Scheme.schemePointSpace (A.toOver ⊗ B.toOver) := by
  let : IsIntegral A.toOver.left := A.variety.property
  let : IsIntegral B.toOver.left := B.variety.property
  let : Smooth A.toOver.hom := A.variety.presentation.smooth
  let : Smooth B.toOver.hom := B.variety.presentation.smooth
  let : IsIntegral (A.toOver ⊗ B.toOver).left :=
    (Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety A.variety B.variety).property
  let : Smooth (A.toOver ⊗ B.toOver).hom :=
    (Albanese.Construction.SegreClosed.tensorSmoothProjectivePresentation A.variety.presentation B.variety.presentation).smooth
  let u : C(ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints B.toOver,
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (A.toOver ⊗ B.toOver)) :=
    ⟨fun p => lift p.1 p.2,
      (HodgeConjecture.DegreeTwo.IntrinsicProductMaps.Constructions.contMDiff_product_map (𝟙 (A.toOver ⊗ B.toOver))).continuous.congr
        (fun p => Category.comp_id (lift p.1 p.2))⟩
  exact TopCat.ofHom u

theorem nativeProductPointMap_fst (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    nativeProductPointMap A B ≫ TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous (fst A.toOver B.toOver)) =
      (TopCat.prodFst (X := Betti.Scheme.schemePointSpace A.toOver) (Y := Betti.Scheme.schemePointSpace B.toOver)) := by
  apply TopCat.ext
  intro p
  exact lift_fst p.1 p.2

theorem nativeProductPointMap_snd (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    nativeProductPointMap A B ≫ TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous (snd A.toOver B.toOver)) =
      (TopCat.prodSnd (X := Betti.Scheme.schemePointSpace A.toOver) (Y := Betti.Scheme.schemePointSpace B.toOver)) := by
  apply TopCat.ext
  intro p
  exact lift_snd p.1 p.2

theorem nativeProductPointMap_mul (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    nativeProductPointMap A A ≫ TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous (MonObj.mul (X := A.toOver))) =
      ChernPairing.nativeMultiplication A := by
  apply TopCat.ext
  intro p
  rfl

theorem nativeProductPointMap_naturality (A B A' B' : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : A.toOver ⟶ A'.toOver) (g : B.toOver ⟶ B'.toOver) :
    nativeProductPointMap A B ≫ TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous (f ⊗ₘ g)) =
      AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map
        ((TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f), TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous g)) :
          (Betti.Scheme.schemePointSpace A.toOver, Betti.Scheme.schemePointSpace B.toOver) ⟶
            (Betti.Scheme.schemePointSpace A'.toOver, Betti.Scheme.schemePointSpace B'.toOver)) ≫ nativeProductPointMap A' B' := by
  apply TopCat.ext
  intro p
  exact lift_map p.1 p.2 f g

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProductPoints
