import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.ProductOver
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SmoothPoints
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ImmersionPointIso
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeImmersionPointTopology

/-! # Product Iso -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Regular.ProductIso.Constructions

noncomputable section

/-! The regular stratum of a genuine complex product is the actual product
of the regular strata. The canonical open immersion is surjective on complex
points and hence is an isomorphism of schemes over the complex base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.CycleClass.Thom.Regular.ProductOver.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SmoothPoints.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.PresentationMap
  Product.SupportTo.Constructions.SmoothOpen Open.ImmersionPointIso.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (πX : Z ⟶ X) (πY : Z ⟶ Y)
  (hprod : IsLimit (BinaryFan.mk πX πY))
  [LocallyOfFinitePresentation X.hom] [LocallyOfFinitePresentation Y.hom]
  [LocallyOfFinitePresentation Z.hom]

def regularProductToAmbient : ProductOver.Constructions.regularProductOver X Y ⟶ Z :=
  Over.homMk (Product.SupportTo.Constructions.PresentationMap.productPresentationMap X Y Z πX πY hprod (ProductOver.Constructions.regularOver X) (ProductOver.Constructions.regularOver Y)
    (ProductOver.Constructions.regularOverInclusion X) (ProductOver.Constructions.regularOverInclusion Y))
    (Product.SupportTo.Constructions.PresentationMap.productPresentationMap_base X Y Z πX πY hprod (ProductOver.Constructions.regularOver X) (ProductOver.Constructions.regularOver Y)
      (ProductOver.Constructions.regularOverInclusion X) (ProductOver.Constructions.regularOverInclusion Y))

instance regularProductToAmbient_open :
    IsOpenImmersion (regularProductToAmbient X Y Z πX πY hprod).left :=
  inferInstanceAs (IsOpenImmersion (Product.SupportTo.Constructions.PresentationMap.productPresentationMap X Y Z πX πY hprod (ProductOver.Constructions.regularOver X) (ProductOver.Constructions.regularOver Y)
    (ProductOver.Constructions.regularOverInclusion X) (ProductOver.Constructions.regularOverInclusion Y)))

def regularProductToRegular : ProductOver.Constructions.regularProductOver X Y ⟶ ProductOver.Constructions.regularOver Z :=
  Over.homMk
    (Product.SupportTo.Constructions.SmoothOpen.openSmoothStratumLift
      (Product.SupportTo.Constructions.PresentationMap.productPresentationMap X Y Z πX πY hprod (ProductOver.Constructions.regularOver X) (ProductOver.Constructions.regularOver Y)
        (ProductOver.Constructions.regularOverInclusion X) (ProductOver.Constructions.regularOverInclusion Y)) Z.hom)
    (by
      change _ ≫ (Geometric.SmoothStratum.smoothStratumι Z.hom ≫ Z.hom) = _
      rw [Product.SupportTo.Constructions.SmoothOpen.openSmoothStratumLift_inclusion_assoc]
      exact Product.SupportTo.Constructions.PresentationMap.productPresentationMap_base X Y Z πX πY hprod (ProductOver.Constructions.regularOver X) (ProductOver.Constructions.regularOver Y)
        (ProductOver.Constructions.regularOverInclusion X) (ProductOver.Constructions.regularOverInclusion Y))

instance regularProductToRegular_open :
    IsOpenImmersion (regularProductToRegular X Y Z πX πY hprod).left :=
  inferInstanceAs (IsOpenImmersion (Product.SupportTo.Constructions.SmoothOpen.openSmoothStratumLift
    (Product.SupportTo.Constructions.PresentationMap.productPresentationMap X Y Z πX πY hprod (ProductOver.Constructions.regularOver X) (ProductOver.Constructions.regularOver Y)
      (ProductOver.Constructions.regularOverInclusion X) (ProductOver.Constructions.regularOverInclusion Y)) Z.hom))

@[reassoc]
theorem regularProductToRegular_inclusion :
    regularProductToRegular X Y Z πX πY hprod ≫ ProductOver.Constructions.regularOverInclusion Z =
      regularProductToAmbient X Y Z πX πY hprod := by
  apply Over.OverMorphism.ext
  exact Product.SupportTo.Constructions.SmoothOpen.openSmoothStratumLift_inclusion _ _

theorem regularProductToRegular_pointSurjective :
    Function.Surjective (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (regularProductToRegular X Y Z πX πY hprod)) := by
  intro z
  let w := z ≫ ProductOver.Constructions.regularOverInclusion Z
  have hz : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying w ∈ Z.hom.smoothLocus := by
    have h : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying w ∈ Set.range (Geometric.SmoothStratum.smoothStratumι Z.hom) :=
      ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying z, rfl⟩
    rw [Geometric.SmoothStratum.range_smoothStratumι] at h
    exact h
  have hs := (Product.SmoothPoints.Constructions.productPoint_smooth_iff X Y Z πX πY hprod w).mp hz
  let b := regularProductToAmbient X Y Z πX πY hprod
  have hr : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying w ∈ Set.range b.left := by
    change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying w ∈ Set.range
      (Product.SupportTo.Constructions.PresentationMap.productPresentationMap X Y Z πX πY hprod (ProductOver.Constructions.regularOver X) (ProductOver.Constructions.regularOver Y)
        (ProductOver.Constructions.regularOverInclusion X) (ProductOver.Constructions.regularOverInclusion Y))
    rw [Product.SupportTo.Constructions.PresentationMap.productPresentationMap_range]
    change πX.left (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying w) ∈ Set.range (Geometric.SmoothStratum.smoothStratumι X.hom) ∧
      πY.left (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying w) ∈ Set.range (Geometric.SmoothStratum.smoothStratumι Y.hom)
    rw [Geometric.SmoothStratum.range_smoothStratumι, Geometric.SmoothStratum.range_smoothStratumι]
    exact hs
  have hw : w ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map b) := by
    rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion]
    exact hr
  obtain ⟨q, hq⟩ := hw
  refine ⟨q, ?_⟩
  apply (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion (ProductOver.Constructions.regularOverInclusion Z)).injective
  change (q ≫ regularProductToRegular X Y Z πX πY hprod) ≫ ProductOver.Constructions.regularOverInclusion Z =
    z ≫ ProductOver.Constructions.regularOverInclusion Z
  rw [Category.assoc, regularProductToRegular_inclusion]
  exact hq

instance regularProductToRegular_isIso :
    IsIso (regularProductToRegular X Y Z πX πY hprod).left :=
  Open.ImmersionPointIso.Constructions.openImmersion_isIso_of_pointSurjective (regularProductToRegular X Y Z πX πY hprod)
    (regularProductToRegular_pointSurjective X Y Z πX πY hprod)

def regularProductOverIso : ProductOver.Constructions.regularProductOver X Y ≅ ProductOver.Constructions.regularOver Z :=
  Over.isoMk (asIso (regularProductToRegular X Y Z πX πY hprod).left)
    (regularProductToRegular X Y Z πX πY hprod).w

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Regular.ProductIso.Constructions
