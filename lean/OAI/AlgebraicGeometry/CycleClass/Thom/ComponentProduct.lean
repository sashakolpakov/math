import OAI.AlgebraicGeometry.CycleClass.Thom.ClopenIntegralComponent
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportTo
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProductIntegral
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveComponent

/-! # Component Product -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.ComponentProduct.Constructions

/-! The actual product of two integral components is an open-and-closed
integral component of the specified product presentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.ClopenIntegralComponent.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.PresentationMap OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProductIntegral.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : IsIntegral V.toOver.left := V.property
local instance (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : LocallyOfFiniteType V.toOver.hom :=
  inferInstanceAs (LocallyOfFiniteType V.structureMap)
local instance (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier) :
    IsOpenImmersion (X.componentInclusionOver C).left := inferInstanceAs (IsOpenImmersion (X.componentInclusion C))
local instance (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier) :
    IsClosedImmersion (X.componentInclusionOver C).left := inferInstanceAs (IsClosedImmersion (X.componentInclusion C))

variable (X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (C : irreducibleComponents X.carrier) (D : irreducibleComponents Y.carrier)

local notation "CX" => OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.toOver (X.componentVariety C)
local notation "DY" => OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.toOver (Y.componentVariety D)

def componentProductOver : Over Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (pullback.fst (CX).hom (DY).hom ≫ (CX).hom)

instance componentProductOver_integral : IsIntegral (componentProductOver X Y C D).left :=
  Scheme.ProductIntegral.Constructions.schemeProduct_isIntegral CX DY

def componentProductFst : componentProductOver X Y C D ⟶ CX := Over.homMk (pullback.fst (CX).hom (DY).hom) rfl

def componentProductSnd : componentProductOver X Y C D ⟶ DY := Over.homMk (pullback.snd (CX).hom (DY).hom) pullback.condition.symm

def componentProductIsLimit : IsLimit (BinaryFan.mk (componentProductFst X Y C D) (componentProductSnd X Y C D)) :=
  (pullbackIsPullback (CX).hom (DY).hom).pullbackConeEquivBinaryFanFunctor

variable (Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
  (hprod : IsLimit (BinaryFan.mk πX πY))

def componentProductMap : componentProductOver X Y C D ⟶ Z.toOver :=
  Over.homMk (Product.SupportTo.Constructions.PresentationMap.productPresentationMap X.toOver Y.toOver Z.toOver πX πY hprod CX DY
    (X.componentInclusionOver C) (Y.componentInclusionOver D))
    (Product.SupportTo.Constructions.PresentationMap.productPresentationMap_base X.toOver Y.toOver Z.toOver πX πY hprod CX DY
      (X.componentInclusionOver C) (Y.componentInclusionOver D))

instance componentProductMap_open : IsOpenImmersion (componentProductMap X Y C D Z πX πY hprod).left :=
  inferInstanceAs (IsOpenImmersion (Product.SupportTo.Constructions.PresentationMap.productPresentationMap X.toOver Y.toOver Z.toOver πX πY hprod CX DY
    (X.componentInclusionOver C) (Y.componentInclusionOver D)))

instance componentProductMap_closed : IsClosedImmersion (componentProductMap X Y C D Z πX πY hprod).left := by
  let i := X.componentInclusionOver C
  let j := Y.componentInclusionOver D
  let : IsClosedImmersion (pullback.map (CX).hom (DY).hom X.toOver.hom Y.toOver.hom i.left j.left (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)
    ((Category.comp_id _).trans i.w.symm) ((Category.comp_id _).trans j.w.symm)) :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance inferInstance i.w.symm j.w.symm
  change IsClosedImmersion (_ ≫ (Product.SupportScheme.Constructions.productPresentationIso X.toOver Y.toOver Z.toOver πX πY hprod).inv)
  infer_instance

def productComponent : irreducibleComponents Z.carrier :=
  ClopenIntegralComponent.Constructions.clopenImageComponent Z (componentProductMap X Y C D Z πX πY hprod).left

theorem productComponent_range : (productComponent X Y C D Z πX πY hprod).val =
    πX.left ⁻¹' C.val ∩ πY.left ⁻¹' D.val := by
  rw [productComponent, ← ClopenIntegralComponent.Constructions.clopenImageComponent_range]
  change Set.range (Product.SupportTo.Constructions.PresentationMap.productPresentationMap X.toOver Y.toOver Z.toOver πX πY hprod CX DY
    (X.componentInclusionOver C) (Y.componentInclusionOver D)) = _
  rw [Product.SupportTo.Constructions.PresentationMap.productPresentationMap_range]
  change πX.left ⁻¹' Set.range (X.componentInclusion C) ∩ πY.left ⁻¹' Set.range (Y.componentInclusion D) = _
  rw [X.componentInclusion_range, Y.componentInclusion_range]

def componentProductOverIso : componentProductOver X Y C D ≅
    (Z.componentVariety (productComponent X Y C D Z πX πY hprod)).toOver :=
  Over.isoMk (ClopenIntegralComponent.Constructions.clopenComponentIso Z (componentProductMap X Y C D Z πX πY hprod).left)
    ((ClopenIntegralComponent.Constructions.clopenComponentMap_base Z (componentProductMap X Y C D Z πX πY hprod).left).trans
      (componentProductMap X Y C D Z πX πY hprod).w)

@[reassoc]
theorem componentProductOverIso_inclusion :
    (componentProductOverIso X Y C D Z πX πY hprod).hom ≫
      Z.componentInclusionOver (productComponent X Y C D Z πX πY hprod) =
      componentProductMap X Y C D Z πX πY hprod := by
  apply Over.OverMorphism.ext
  exact ClopenIntegralComponent.Constructions.clopenComponentMap_inclusion Z (componentProductMap X Y C D Z πX πY hprod).left

end AlgebraicGeometry.CycleClass.Thom.ComponentProduct.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.ComponentProduct.Constructions.Projections

/-! Actual product projections from the native product component, with its
universal property and the genuine ambient inclusion squares. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.ComponentProduct.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (C : irreducibleComponents X.carrier) (D : irreducibleComponents Y.carrier)
  (Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
  (hprod : IsLimit (BinaryFan.mk πX πY))

@[reassoc]
theorem componentProductMap_fst : componentProductMap X Y C D Z πX πY hprod ≫ πX =
    componentProductFst X Y C D ≫ X.componentInclusionOver C := by
  apply Over.OverMorphism.ext
  have he : (Product.SupportScheme.Constructions.productPresentationIso X.toOver Y.toOver Z.toOver πX πY hprod).inv ≫ πX.left =
      pullback.fst X.toOver.hom Y.toOver.hom := by
    rw [← Product.SupportScheme.Constructions.productPresentationIso_hom_fst X.toOver Y.toOver Z.toOver πX πY hprod]
    exact (Product.SupportScheme.Constructions.productPresentationIso X.toOver Y.toOver Z.toOver πX πY hprod).inv_hom_id_assoc _
  change (_ ≫ (Product.SupportScheme.Constructions.productPresentationIso X.toOver Y.toOver Z.toOver πX πY hprod).inv) ≫ πX.left = _
  rw [Category.assoc, he]
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem componentProductMap_snd : componentProductMap X Y C D Z πX πY hprod ≫ πY =
    componentProductSnd X Y C D ≫ Y.componentInclusionOver D := by
  apply Over.OverMorphism.ext
  have he : (Product.SupportScheme.Constructions.productPresentationIso X.toOver Y.toOver Z.toOver πX πY hprod).inv ≫ πY.left =
      pullback.snd X.toOver.hom Y.toOver.hom := by
    rw [← Product.SupportScheme.Constructions.productPresentationIso_hom_snd X.toOver Y.toOver Z.toOver πX πY hprod]
    exact (Product.SupportScheme.Constructions.productPresentationIso X.toOver Y.toOver Z.toOver πX πY hprod).inv_hom_id_assoc _
  change (_ ≫ (Product.SupportScheme.Constructions.productPresentationIso X.toOver Y.toOver Z.toOver πX πY hprod).inv) ≫ πY.left = _
  rw [Category.assoc, he]
  exact pullback.lift_snd _ _ _

def productComponentFst : (Z.componentVariety (productComponent X Y C D Z πX πY hprod)).toOver ⟶
    (X.componentVariety C).toOver :=
  (componentProductOverIso X Y C D Z πX πY hprod).inv ≫ componentProductFst X Y C D

def productComponentSnd : (Z.componentVariety (productComponent X Y C D Z πX πY hprod)).toOver ⟶
    (Y.componentVariety D).toOver :=
  (componentProductOverIso X Y C D Z πX πY hprod).inv ≫ componentProductSnd X Y C D

def productComponentIsLimit : IsLimit (BinaryFan.mk
    (productComponentFst X Y C D Z πX πY hprod) (productComponentSnd X Y C D Z πX πY hprod)) :=
  IsLimit.ofIsoLimit (componentProductIsLimit X Y C D)
    (BinaryFan.ext (componentProductOverIso X Y C D Z πX πY hprod)
      (by simp only [BinaryFan.mk_fst, productComponentFst, Iso.hom_inv_id_assoc])
      (by simp only [BinaryFan.mk_snd, productComponentSnd, Iso.hom_inv_id_assoc]))

@[reassoc]
theorem productComponentFst_inclusion :
    productComponentFst X Y C D Z πX πY hprod ≫ X.componentInclusionOver C =
      Z.componentInclusionOver (productComponent X Y C D Z πX πY hprod) ≫ πX := by
  apply (cancel_epi (componentProductOverIso X Y C D Z πX πY hprod).hom).mp
  simp only [productComponentFst, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, componentProductOverIso_inclusion, componentProductMap_fst]

@[reassoc]
theorem productComponentSnd_inclusion :
    productComponentSnd X Y C D Z πX πY hprod ≫ Y.componentInclusionOver D =
      Z.componentInclusionOver (productComponent X Y C D Z πX πY hprod) ≫ πY := by
  apply (cancel_epi (componentProductOverIso X Y C D Z πX πY hprod).hom).mp
  simp only [productComponentSnd, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, componentProductOverIso_inclusion, componentProductMap_snd]

end AlgebraicGeometry.CycleClass.Thom.ComponentProduct.Constructions.Projections

end

end OAI
