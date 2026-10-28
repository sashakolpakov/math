import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.ProductIso
import OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticProductMaps

/-! # Product Projections -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Regular.ProductProjections.Constructions

noncomputable section

/-! Genuine projections from the regular stratum of a product and their
holomorphic point-space product identification. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Regular.ProductOver.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Regular.ProductIso.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.PresentationMap
  Product.SupportScheme.Constructions Product.PresentationPoints.Constructions AnalyticProductMaps.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (πX : Z ⟶ X) (πY : Z ⟶ Y)
  (hprod : IsLimit (BinaryFan.mk πX πY))
  [LocallyOfFinitePresentation X.hom] [LocallyOfFinitePresentation Y.hom]
  [LocallyOfFinitePresentation Z.hom]

def regularFst : ProductOver.Constructions.regularOver Z ⟶ ProductOver.Constructions.regularOver X :=
  (ProductIso.Constructions.regularProductOverIso X Y Z πX πY hprod).inv ≫ ProductOver.Constructions.regularProductFst X Y

def regularSnd : ProductOver.Constructions.regularOver Z ⟶ ProductOver.Constructions.regularOver Y :=
  (ProductIso.Constructions.regularProductOverIso X Y Z πX πY hprod).inv ≫ ProductOver.Constructions.regularProductSnd X Y

def regularIsLimit : IsLimit (BinaryFan.mk (regularFst X Y Z πX πY hprod)
    (regularSnd X Y Z πX πY hprod)) :=
  IsLimit.ofIsoLimit (ProductOver.Constructions.regularProductIsLimit X Y)
    (BinaryFan.ext (ProductIso.Constructions.regularProductOverIso X Y Z πX πY hprod)
      (by simp only [BinaryFan.mk_fst, regularFst, Iso.hom_inv_id_assoc])
      (by simp only [BinaryFan.mk_snd, regularSnd, Iso.hom_inv_id_assoc]))

omit [LocallyOfFinitePresentation Z.hom] in
@[reassoc]
theorem regularProductToAmbient_fst :
    ProductIso.Constructions.regularProductToAmbient X Y Z πX πY hprod ≫ πX =
      ProductOver.Constructions.regularProductFst X Y ≫ ProductOver.Constructions.regularOverInclusion X := by
  apply Over.OverMorphism.ext
  have he : (Product.SupportScheme.Constructions.productPresentationIso X Y Z πX πY hprod).inv ≫ πX.left = pullback.fst X.hom Y.hom := by
    rw [← Product.SupportScheme.Constructions.productPresentationIso_hom_fst X Y Z πX πY hprod]
    exact (Product.SupportScheme.Constructions.productPresentationIso X Y Z πX πY hprod).inv_hom_id_assoc _
  change (_ ≫ (Product.SupportScheme.Constructions.productPresentationIso X Y Z πX πY hprod).inv) ≫ πX.left = _
  rw [Category.assoc, he]
  exact pullback.lift_fst _ _ _

omit [LocallyOfFinitePresentation Z.hom] in
@[reassoc]
theorem regularProductToAmbient_snd :
    ProductIso.Constructions.regularProductToAmbient X Y Z πX πY hprod ≫ πY =
      ProductOver.Constructions.regularProductSnd X Y ≫ ProductOver.Constructions.regularOverInclusion Y := by
  apply Over.OverMorphism.ext
  have he : (Product.SupportScheme.Constructions.productPresentationIso X Y Z πX πY hprod).inv ≫ πY.left = pullback.snd X.hom Y.hom := by
    rw [← Product.SupportScheme.Constructions.productPresentationIso_hom_snd X Y Z πX πY hprod]
    exact (Product.SupportScheme.Constructions.productPresentationIso X Y Z πX πY hprod).inv_hom_id_assoc _
  change (_ ≫ (Product.SupportScheme.Constructions.productPresentationIso X Y Z πX πY hprod).inv) ≫ πY.left = _
  rw [Category.assoc, he]
  exact pullback.lift_snd _ _ _

@[reassoc]
theorem regularFst_inclusion :
    regularFst X Y Z πX πY hprod ≫ ProductOver.Constructions.regularOverInclusion X =
      ProductOver.Constructions.regularOverInclusion Z ≫ πX := by
  apply (cancel_epi (ProductIso.Constructions.regularProductOverIso X Y Z πX πY hprod).hom).mp
  simp only [regularFst, Category.assoc, Iso.hom_inv_id_assoc]
  change _ = ProductIso.Constructions.regularProductToRegular X Y Z πX πY hprod ≫ (ProductOver.Constructions.regularOverInclusion Z ≫ πX)
  rw [← Category.assoc, ProductIso.Constructions.regularProductToRegular_inclusion, regularProductToAmbient_fst]

@[reassoc]
theorem regularSnd_inclusion :
    regularSnd X Y Z πX πY hprod ≫ ProductOver.Constructions.regularOverInclusion Y =
      ProductOver.Constructions.regularOverInclusion Z ≫ πY := by
  apply (cancel_epi (ProductIso.Constructions.regularProductOverIso X Y Z πX πY hprod).hom).mp
  simp only [regularSnd, Category.assoc, Iso.hom_inv_id_assoc]
  change _ = ProductIso.Constructions.regularProductToRegular X Y Z πX πY hprod ≫ (ProductOver.Constructions.regularOverInclusion Z ≫ πY)
  rw [← Category.assoc, ProductIso.Constructions.regularProductToRegular_inclusion, regularProductToAmbient_snd]

def regularProductPointsHomeomorph : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ProductOver.Constructions.regularOver Z) ≃ₜ
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ProductOver.Constructions.regularOver X) × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ProductOver.Constructions.regularOver Y)) :=
  Product.PresentationPoints.Constructions.productPresentationPointsHomeomorph (ProductOver.Constructions.regularOver X) (ProductOver.Constructions.regularOver Y) (ProductOver.Constructions.regularOver Z)
    (regularFst X Y Z πX πY hprod) (regularSnd X Y Z πX πY hprod)
    (regularIsLimit X Y Z πX πY hprod)

variable [IsIntegral X.left] [IsIntegral Y.left] [IsIntegral Z.left]

local notation "ModelX" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Over.hom (OAI.AlgebraicGeometry.CycleClass.Thom.Regular.ProductOver.Constructions.regularOver X))) → ℂ
local notation "ModelY" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Over.hom (OAI.AlgebraicGeometry.CycleClass.Thom.Regular.ProductOver.Constructions.regularOver Y))) → ℂ
local notation "ModelZ" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Over.hom (OAI.AlgebraicGeometry.CycleClass.Thom.Regular.ProductOver.Constructions.regularOver Z))) → ℂ

theorem regularProductPointsHomeomorph_contMDiff (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, ModelZ) (𝓘(ℂ, ModelX).prod 𝓘(ℂ, ModelY)) r
      (regularProductPointsHomeomorph X Y Z πX πY hprod) :=
  AnalyticProductMaps.Constructions.productPresentationPointsHomeomorph_contMDiff _ _ _ r

theorem regularProductPointsHomeomorph_symm_contMDiff (r : ℕ∞ω) :
    ContMDiff (𝓘(ℂ, ModelX).prod 𝓘(ℂ, ModelY)) 𝓘(ℂ, ModelZ) r
      (regularProductPointsHomeomorph X Y Z πX πY hprod).symm :=
  AnalyticProductMaps.Constructions.productPresentationPointsHomeomorph_symm_contMDiff _ _ _ r

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Regular.ProductProjections.Constructions
