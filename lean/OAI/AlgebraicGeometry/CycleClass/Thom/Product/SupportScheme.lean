import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProductIntegral
import OAI.AlgebraicGeometry.CycleClass.Geometric.StratumClosure
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-! # Support Scheme -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme.Constructions

noncomputable section

/-! The actual product of reduced integral closed supports is the reduced
integral closed scheme on their inverse-image intersection in any genuine
product presentation. No cohomological property defines this support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProductIntegral.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase)
  (A : IrreducibleCloseds X.left) (B : IrreducibleCloseds Y.left)

abbrev productSupportScheme : Scheme :=
  pullback (Geometric.SupportFiniteType.supportStructureMap A X.hom) (Geometric.SupportFiniteType.supportStructureMap B Y.hom)

instance productSupportScheme_integral [LocallyOfFiniteType X.hom] :
    IsIntegral (productSupportScheme X Y A B) := by
  let XA := Over.mk (Geometric.SupportFiniteType.supportStructureMap A X.hom)
  let YB := Over.mk (Geometric.SupportFiniteType.supportStructureMap B Y.hom)
  let : LocallyOfFiniteType XA.hom := Geometric.SupportFiniteType.supportStructureMap_locallyOfFiniteType A X.hom
  let : IsIntegral XA.left := Geometric.GenericPoint.reducedSupportScheme_isIntegral A
  let : IsIntegral YB.left := Geometric.GenericPoint.reducedSupportScheme_isIntegral B
  exact Thom.Scheme.ProductIntegral.Constructions.schemeProduct_isIntegral XA YB

def productSupportPullbackMap : productSupportScheme X Y A B ⟶ pullback X.hom Y.hom :=
  pullback.map (Geometric.SupportFiniteType.supportStructureMap A X.hom) (Geometric.SupportFiniteType.supportStructureMap B Y.hom) X.hom Y.hom
    (Geometric.GenericPoint.reducedSupportι A) (Geometric.GenericPoint.reducedSupportι B) (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)
    (Category.comp_id _) (Category.comp_id _)

instance productSupportPullbackMap_closed : IsClosedImmersion (productSupportPullbackMap X Y A B) := by
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (inferInstance : IsClosedImmersion (Geometric.GenericPoint.reducedSupportι A))
    (inferInstance : IsClosedImmersion (Geometric.GenericPoint.reducedSupportι B)) rfl rfl

theorem productSupportPullbackMap_range :
    Set.range (productSupportPullbackMap X Y A B) =
      pullback.fst X.hom Y.hom ⁻¹' (A : Set X.left) ∩
        pullback.snd X.hom Y.hom ⁻¹' (B : Set Y.left) := by
  unfold productSupportPullbackMap
  rw [Scheme.Pullback.range_map, Geometric.GenericPoint.range_reducedSupportι, Geometric.GenericPoint.range_reducedSupportι]

variable (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (πX : Z ⟶ X) (πY : Z ⟶ Y)
  (hprod : IsLimit (BinaryFan.mk πX πY))

def productPresentationIso : Z.left ≅ pullback X.hom Y.hom :=
  (Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk πX πY) hprod).isoPullback

@[reassoc]
theorem productPresentationIso_hom_fst :
    (productPresentationIso X Y Z πX πY hprod).hom ≫ pullback.fst X.hom Y.hom = πX.left :=
  IsPullback.isoPullback_hom_fst _

@[reassoc]
theorem productPresentationIso_hom_snd :
    (productPresentationIso X Y Z πX πY hprod).hom ≫ pullback.snd X.hom Y.hom = πY.left :=
  IsPullback.isoPullback_hom_snd _

def productSupportInclusion : productSupportScheme X Y A B ⟶ Z.left :=
  productSupportPullbackMap X Y A B ≫ (productPresentationIso X Y Z πX πY hprod).inv

instance productSupportInclusion_closed :
    IsClosedImmersion (productSupportInclusion X Y A B Z πX πY hprod) := by
  unfold productSupportInclusion
  infer_instance

theorem productSupportInclusion_range :
    Set.range (productSupportInclusion X Y A B Z πX πY hprod) =
      πX.left ⁻¹' (A : Set X.left) ∩ πY.left ⁻¹' (B : Set Y.left) := by
  let e := productPresentationIso X Y Z πX πY hprod
  have hc : productSupportInclusion X Y A B Z πX πY hprod ≫ e.hom =
      productSupportPullbackMap X Y A B := by
    simp only [productSupportInclusion, e, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hr : Set.range (productSupportInclusion X Y A B Z πX πY hprod) =
      e.hom ⁻¹' Set.range (productSupportPullbackMap X Y A B) := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, (congrArg (fun f : productSupportScheme X Y A B ⟶ pullback X.hom Y.hom => f t) hc).symm⟩
    · rintro ⟨t, ht⟩
      refine ⟨t, e.hom.isOpenEmbedding.injective ?_⟩
      change (productSupportInclusion X Y A B Z πX πY hprod ≫ e.hom) t = e.hom z
      rw [hc]
      exact ht
  rw [hr, productSupportPullbackMap_range]
  ext z
  change (pullback.fst X.hom Y.hom (e.hom z) ∈ (A : Set X.left) ∧
    pullback.snd X.hom Y.hom (e.hom z) ∈ (B : Set Y.left)) ↔ _
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    productPresentationIso_hom_fst, productPresentationIso_hom_snd]
  rfl

variable [LocallyOfFiniteType X.hom]

def productIrreducibleSupport : IrreducibleCloseds Z.left :=
  Geometric.StratumClosure.integralImageClosure (productSupportInclusion X Y A B Z πX πY hprod)

theorem productIrreducibleSupport_coe :
    (productIrreducibleSupport X Y A B Z πX πY hprod : Set Z.left) =
      πX.left ⁻¹' (A : Set X.left) ∩ πY.left ⁻¹' (B : Set Y.left) := by
  change closure (Set.range (productSupportInclusion X Y A B Z πX πY hprod)) = _
  rw [(productSupportInclusion X Y A B Z πX πY hprod).isClosedEmbedding.isClosed_range.closure_eq,
    productSupportInclusion_range]

/-- An isomorphism of actual reduced schemes, not only their underlying sets. -/
def productSupportReducedIso : productSupportScheme X Y A B ≅
    Geometric.GenericPoint.reducedSupportScheme (productIrreducibleSupport X Y A B Z πX πY hprod) :=
  asIso (productSupportInclusion X Y A B Z πX πY hprod).toImage ≪≫
    Geometric.StratumClosure.reducedImageClosureIso (productSupportInclusion X Y A B Z πX πY hprod)

@[reassoc]
theorem productSupportReducedIso_inclusion :
    (productSupportReducedIso X Y A B Z πX πY hprod).hom ≫
      Geometric.GenericPoint.reducedSupportι (productIrreducibleSupport X Y A B Z πX πY hprod) =
        productSupportInclusion X Y A B Z πX πY hprod :=
  Geometric.StratumClosure.toReducedImageClosure_inclusion _

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme.Constructions
