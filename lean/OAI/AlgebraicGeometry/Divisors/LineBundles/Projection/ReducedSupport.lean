import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportOverIso

/-! # Reduced Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.ReducedSupport.BundleCycles

noncomputable section

/-! The actual inverse image of an integral closed support under a product
projection is a reduced integral closed scheme, with its genuine product
presentation. No cycle or cohomology law defines this support. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.Dimension
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProductIntegral.Constructions

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    (B : IrreducibleCloseds Y.left)

def projectionSupportScheme : Scheme := pullback X.hom (CycleClass.Geometric.SupportFiniteType.supportStructureMap B Y.hom)

instance projectionSupportScheme_integral : IsIntegral (projectionSupportScheme X Y B) := by
  let YB := Over.mk (CycleClass.Geometric.SupportFiniteType.supportStructureMap B Y.hom)
  let : IsIntegral YB.left := CycleClass.Geometric.GenericPoint.reducedSupportScheme_isIntegral B
  exact CycleClass.Thom.Scheme.ProductIntegral.Constructions.schemeProduct_isIntegral X YB

def projectionSupportPullbackMap : projectionSupportScheme X Y B ⟶ pullback X.hom Y.hom :=
  pullback.map X.hom (CycleClass.Geometric.SupportFiniteType.supportStructureMap B Y.hom) X.hom Y.hom (𝟙 X.left) (CycleClass.Geometric.GenericPoint.reducedSupportι B)
    (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) (by simp) (Category.comp_id _)

instance projectionSupportPullbackMap_closed : IsClosedImmersion (projectionSupportPullbackMap X Y B) := by
  let : MorphismProperty.IsStableUnderComposition (@IsClosedImmersion.{0}) :=
    { comp_mem := fun f g hf hg => @IsClosedImmersion.comp _ _ _ f g hf hg }
  have h := MorphismProperty.pullbackMap (P := @IsClosedImmersion.{0})
    (f := X.hom) (g := CycleClass.Geometric.SupportFiniteType.supportStructureMap B Y.hom) (f' := X.hom) (g' := Y.hom)
    (inferInstance : IsClosedImmersion (𝟙 X.left))
    (inferInstance : IsClosedImmersion (CycleClass.Geometric.GenericPoint.reducedSupportι B)) (Category.id_comp _).symm rfl
  exact h

omit [IsIntegral X.left] [LocallyOfFiniteType X.hom] in
theorem projectionSupportPullbackMap_range :
    Set.range (projectionSupportPullbackMap X Y B) = pullback.snd X.hom Y.hom ⁻¹' (B : Set Y.left) := by
  have h := Scheme.Pullback.range_map X.hom (CycleClass.Geometric.SupportFiniteType.supportStructureMap B Y.hom) X.hom Y.hom
    (𝟙 X.left) (CycleClass.Geometric.GenericPoint.reducedSupportι B) (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) (by simp) (Category.comp_id _)
  rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι] at h
  simp only [Scheme.Hom.id_base, TopCat.coe_id, Set.range_id, Set.preimage_univ, Set.univ_inter] at h
  exact h

variable (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (πX : Z ⟶ X) (πY : Z ⟶ Y)
    (hprod : IsLimit (BinaryFan.mk πX πY))

def projectionSupportMap : projectionSupportScheme X Y B ⟶ Z.left :=
  projectionSupportPullbackMap X Y B ≫ (CycleClass.Thom.Product.SupportScheme.Constructions.productPresentationIso X Y Z πX πY hprod).inv

instance projectionSupportMap_closed : IsClosedImmersion (projectionSupportMap X Y B Z πX πY hprod) := by
  unfold projectionSupportMap
  infer_instance

omit [IsIntegral X.left] [LocallyOfFiniteType X.hom] in
theorem projectionSupportMap_range :
    Set.range (projectionSupportMap X Y B Z πX πY hprod) = πY.left ⁻¹' (B : Set Y.left) := by
  let e := CycleClass.Thom.Product.SupportScheme.Constructions.productPresentationIso X Y Z πX πY hprod
  have hc : projectionSupportMap X Y B Z πX πY hprod ≫ e.hom = projectionSupportPullbackMap X Y B := by
    change (_ ≫ e.inv) ≫ e.hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hr : Set.range (projectionSupportMap X Y B Z πX πY hprod) =
      e.hom ⁻¹' Set.range (projectionSupportPullbackMap X Y B) := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, (congrArg (fun k => k t) hc).symm⟩
    · rintro ⟨t, ht⟩
      refine ⟨t, e.hom.isOpenEmbedding.injective ?_⟩
      change (projectionSupportMap X Y B Z πX πY hprod ≫ e.hom) t = e.hom z
      rw [hc]
      exact ht
  rw [hr, projectionSupportPullbackMap_range]
  ext z
  change pullback.snd X.hom Y.hom (e.hom z) ∈ (B : Set Y.left) ↔ _
  rw [← Scheme.Hom.comp_apply, CycleClass.Thom.Product.SupportScheme.Constructions.productPresentationIso_hom_snd]
  rfl

def projectionIrreducibleSupport : IrreducibleCloseds Z.left :=
  CycleClass.Geometric.StratumClosure.integralImageClosure (projectionSupportMap X Y B Z πX πY hprod)

theorem projectionIrreducibleSupport_coe :
    (projectionIrreducibleSupport X Y B Z πX πY hprod : Set Z.left) = πY.left ⁻¹' (B : Set Y.left) := by
  change closure (Set.range (projectionSupportMap X Y B Z πX πY hprod)) = _
  rw [(projectionSupportMap X Y B Z πX πY hprod).isClosedEmbedding.isClosed_range.closure_eq,
    projectionSupportMap_range]

def projectionSupportReducedIso : projectionSupportScheme X Y B ≅
    CycleClass.Geometric.GenericPoint.reducedSupportScheme (projectionIrreducibleSupport X Y B Z πX πY hprod) :=
  asIso (projectionSupportMap X Y B Z πX πY hprod).toImage ≪≫
    CycleClass.Geometric.StratumClosure.reducedImageClosureIso (projectionSupportMap X Y B Z πX πY hprod)

theorem projectionSupportReducedIso_inclusion :
    (projectionSupportReducedIso X Y B Z πX πY hprod).hom ≫
      CycleClass.Geometric.GenericPoint.reducedSupportι (projectionIrreducibleSupport X Y B Z πX πY hprod) =
      projectionSupportMap X Y B Z πX πY hprod := CycleClass.Geometric.StratumClosure.toReducedImageClosure_inclusion _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.ReducedSupport.BundleCycles
