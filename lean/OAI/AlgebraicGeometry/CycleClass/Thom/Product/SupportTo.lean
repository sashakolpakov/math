import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProductDimension
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme
import OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimension
import OAI.AlgebraicGeometry.CycleClass.Geometric.SmoothStratum

/-! # Support To -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.Dimension

/-! Dimension of the genuine reduced closed product support, transported
through its actual scheme isomorphism over the complex base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProductDimension.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase)
  (A : IrreducibleCloseds X.left) (B : IrreducibleCloseds Y.left)
  (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (πX : Z ⟶ X) (πY : Z ⟶ Y)
  (hprod : IsLimit (BinaryFan.mk πX πY))

@[reassoc]
theorem productPresentationIso_base :
    (SupportScheme.Constructions.productPresentationIso X Y Z πX πY hprod).hom ≫ (pullback.fst X.hom Y.hom ≫ X.hom) =
      Z.hom := by
  rw [SupportScheme.Constructions.productPresentationIso_hom_fst_assoc]
  exact πX.w

@[reassoc]
theorem productSupportInclusion_base :
    SupportScheme.Constructions.productSupportInclusion X Y A B Z πX πY hprod ≫ Z.hom =
      pullback.fst (Geometric.SupportFiniteType.supportStructureMap A X.hom) (Geometric.SupportFiniteType.supportStructureMap B Y.hom) ≫
        Geometric.SupportFiniteType.supportStructureMap A X.hom := by
  let e := SupportScheme.Constructions.productPresentationIso X Y Z πX πY hprod
  have he : e.inv ≫ Z.hom = pullback.fst X.hom Y.hom ≫ X.hom := by
    rw [← productPresentationIso_base X Y Z πX πY hprod]
    exact e.inv_hom_id_assoc _
  change (SupportScheme.Constructions.productSupportPullbackMap X Y A B ≫ e.inv) ≫ Z.hom = _
  rw [Category.assoc, he, ← Category.assoc]
  have hp : SupportScheme.Constructions.productSupportPullbackMap X Y A B ≫ pullback.fst X.hom Y.hom =
      pullback.fst (Geometric.SupportFiniteType.supportStructureMap A X.hom) (Geometric.SupportFiniteType.supportStructureMap B Y.hom) ≫ Geometric.GenericPoint.reducedSupportι A :=
    pullback.lift_fst _ _ _
  rw [hp, Category.assoc]
  rfl

variable [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]

theorem productIrreducibleSupport_dimension :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod) Z.hom =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension A X.hom + Foundations.Scheme.SupportDimension.supportTranscendenceDimension B Y.hom := by
  let XA := Over.mk (Geometric.SupportFiniteType.supportStructureMap A X.hom)
  let YB := Over.mk (Geometric.SupportFiniteType.supportStructureMap B Y.hom)
  let : LocallyOfFiniteType XA.hom := Geometric.SupportFiniteType.supportStructureMap_locallyOfFiniteType A X.hom
  let : LocallyOfFiniteType YB.hom := Geometric.SupportFiniteType.supportStructureMap_locallyOfFiniteType B Y.hom
  let : IsIntegral XA.left := Geometric.GenericPoint.reducedSupportScheme_isIntegral A
  let : IsIntegral YB.left := Geometric.GenericPoint.reducedSupportScheme_isIntegral B
  have h := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion
    (SupportScheme.Constructions.productSupportReducedIso X Y A B Z πX πY hprod).hom
    (Geometric.SupportFiniteType.supportStructureMap (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod) Z.hom)
  have hb : (SupportScheme.Constructions.productSupportReducedIso X Y A B Z πX πY hprod).hom ≫
      Geometric.SupportFiniteType.supportStructureMap (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod) Z.hom =
      pullback.fst XA.hom YB.hom ≫ XA.hom := by
    unfold Geometric.SupportFiniteType.supportStructureMap
    rw [SupportScheme.Constructions.productSupportReducedIso_inclusion_assoc, productSupportInclusion_base]
    rfl
  rw [hb] at h
  exact h.symm.trans (Thom.Scheme.ProductDimension.Constructions.schemeProduct_dimension XA YB)

end AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.Dimension

namespace AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.PresentationMap

/-! Actual maps from fiber products into a specified product presentation,
including their ranges, base compatibility, and open-immersion property. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.Dimension

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (πX : Z ⟶ X) (πY : Z ⟶ Y)
  (hprod : IsLimit (BinaryFan.mk πX πY))
  (U V : Over Foundations.Scheme.ProjectiveSpace.complexBase) (i : U ⟶ X) (j : V ⟶ Y)

def productPresentationMap : pullback U.hom V.hom ⟶ Z.left :=
  pullback.map U.hom V.hom X.hom Y.hom i.left j.left (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)
    ((Category.comp_id _).trans i.w.symm) ((Category.comp_id _).trans j.w.symm) ≫
    (SupportScheme.Constructions.productPresentationIso X Y Z πX πY hprod).inv

instance productPresentationMap_open [IsOpenImmersion i.left] [IsOpenImmersion j.left] :
    IsOpenImmersion (productPresentationMap X Y Z πX πY hprod U V i j) := by
  let : IsOpenImmersion (pullback.map U.hom V.hom X.hom Y.hom i.left j.left (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)
    ((Category.comp_id _).trans i.w.symm) ((Category.comp_id _).trans j.w.symm)) :=
      MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance i.w.symm j.w.symm
  unfold productPresentationMap
  infer_instance

@[reassoc]
theorem productPresentationMap_base :
    productPresentationMap X Y Z πX πY hprod U V i j ≫ Z.hom =
      pullback.fst U.hom V.hom ≫ U.hom := by
  let e := SupportScheme.Constructions.productPresentationIso X Y Z πX πY hprod
  have he : e.inv ≫ Z.hom = pullback.fst X.hom Y.hom ≫ X.hom := by
    rw [← Dimension.productPresentationIso_base X Y Z πX πY hprod]
    exact e.inv_hom_id_assoc _
  unfold productPresentationMap
  rw [Category.assoc, he, ← Category.assoc, pullback.map, pullback.lift_fst, Category.assoc, i.w]

theorem productPresentationMap_range :
    Set.range (productPresentationMap X Y Z πX πY hprod U V i j) =
      πX.left ⁻¹' Set.range i.left ∩ πY.left ⁻¹' Set.range j.left := by
  let e := SupportScheme.Constructions.productPresentationIso X Y Z πX πY hprod
  let m := pullback.map U.hom V.hom X.hom Y.hom i.left j.left (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)
    ((Category.comp_id _).trans i.w.symm) ((Category.comp_id _).trans j.w.symm)
  have hc : productPresentationMap X Y Z πX πY hprod U V i j ≫ e.hom = m := by
    simp only [productPresentationMap, e, m, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hr : Set.range (productPresentationMap X Y Z πX πY hprod U V i j) =
      e.hom ⁻¹' Set.range m := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, (congrArg (fun f : pullback U.hom V.hom ⟶ pullback X.hom Y.hom => f t) hc).symm⟩
    · rintro ⟨t, ht⟩
      refine ⟨t, e.hom.isOpenEmbedding.injective ?_⟩
      change (productPresentationMap X Y Z πX πY hprod U V i j ≫ e.hom) t = e.hom z
      rw [hc]
      exact ht
  rw [hr]
  dsimp only [m]
  rw [Scheme.Pullback.range_map]
  ext z
  change (pullback.fst X.hom Y.hom (e.hom z) ∈ Set.range i.left ∧
    pullback.snd X.hom Y.hom (e.hom z) ∈ Set.range j.left) ↔ _
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    SupportScheme.Constructions.productPresentationIso_hom_fst, SupportScheme.Constructions.productPresentationIso_hom_snd]
  rfl

end AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.PresentationMap

namespace AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.SmoothOpen

/-! Products of actual smooth open subschemes lie in the genuine smooth
locus of the product. The resulting factorization is an open immersion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.PresentationMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem schemeProduct_smooth (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [Smooth Y.hom] :
    Smooth (pullback.fst X.hom Y.hom ≫ X.hom) := inferInstance

theorem openImmersion_range_subset_smoothLocus {U X Y : Scheme}
    (i : U ⟶ X) (f : X ⟶ Y) [IsOpenImmersion i] [LocallyOfFinitePresentation f]
    [Smooth (i ≫ f)] : Set.range i ⊆ (f.smoothLocus : Set X) := by
  rintro _ ⟨u, rfl⟩
  have h := Scheme.Hom.preimage_smoothLocus_eq i f
  rw [Scheme.Hom.smoothLocus_eq_top (i ≫ f)] at h
  have hu : u ∈ (i ⁻¹ᵁ f.smoothLocus) := by rw [h]; trivial
  exact hu

def openSmoothStratumLift {U X Y : Scheme}
    (i : U ⟶ X) (f : X ⟶ Y) [IsOpenImmersion i] [LocallyOfFinitePresentation f]
    [Smooth (i ≫ f)] : U ⟶ Geometric.SmoothStratum.smoothStratum f :=
  IsOpenImmersion.lift (Geometric.SmoothStratum.smoothStratumι f) i (by
    rw [Geometric.SmoothStratum.range_smoothStratumι]
    exact openImmersion_range_subset_smoothLocus i f)

instance openSmoothStratumLift_open {U X Y : Scheme}
    (i : U ⟶ X) (f : X ⟶ Y) [IsOpenImmersion i] [LocallyOfFinitePresentation f]
    [Smooth (i ≫ f)] : IsOpenImmersion (openSmoothStratumLift i f) := by
  unfold openSmoothStratumLift
  infer_instance

@[reassoc]
theorem openSmoothStratumLift_inclusion {U X Y : Scheme}
    (i : U ⟶ X) (f : X ⟶ Y) [IsOpenImmersion i] [LocallyOfFinitePresentation f]
    [Smooth (i ≫ f)] : openSmoothStratumLift i f ≫ Geometric.SmoothStratum.smoothStratumι f = i :=
  IsOpenImmersion.lift_fac _ _ _

variable (X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (πX : Z ⟶ X) (πY : Z ⟶ Y)
  (hprod : IsLimit (BinaryFan.mk πX πY))
  (U V : Over Foundations.Scheme.ProjectiveSpace.complexBase) (i : U ⟶ X) (j : V ⟶ Y)
  [IsOpenImmersion i.left] [IsOpenImmersion j.left]
  [Smooth U.hom] [Smooth V.hom]

instance productPresentationMap_smooth_base :
    Smooth (PresentationMap.productPresentationMap X Y Z πX πY hprod U V i j ≫ Z.hom) := by
  rw [PresentationMap.productPresentationMap_base]
  exact schemeProduct_smooth U V

theorem productOpen_range_subset_smoothLocus [LocallyOfFinitePresentation Z.hom] :
    Set.range (PresentationMap.productPresentationMap X Y Z πX πY hprod U V i j) ⊆ (Z.hom.smoothLocus : Set Z.left) :=
  openImmersion_range_subset_smoothLocus
    (PresentationMap.productPresentationMap X Y Z πX πY hprod U V i j) Z.hom

end AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.SmoothOpen

namespace AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.RegularStratum

/-! The product of the two actual regular strata is a genuine dense open
subscheme of the regular stratum of the reduced product support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.Dimension OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.SmoothOpen
  Thom.Scheme.ProductIntegral.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase)
  (A : IrreducibleCloseds X.left) (B : IrreducibleCloseds Y.left)
  [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]

abbrev productRegularScheme : Scheme :=
  pullback (Geometric.SmoothStratum.smoothStratumToBase (Geometric.SupportFiniteType.supportStructureMap A X.hom))
    (Geometric.SmoothStratum.smoothStratumToBase (Geometric.SupportFiniteType.supportStructureMap B Y.hom))

instance productRegularScheme_integral : IsIntegral (productRegularScheme X Y A B) := by
  let U := Over.mk (Geometric.SmoothStratum.smoothStratumToBase (Geometric.SupportFiniteType.supportStructureMap A X.hom))
  let V := Over.mk (Geometric.SmoothStratum.smoothStratumToBase (Geometric.SupportFiniteType.supportStructureMap B Y.hom))
  let : IsIntegral U.left := inferInstanceAs (IsIntegral (Geometric.SmoothStratum.smoothStratum (Geometric.SupportFiniteType.supportStructureMap A X.hom)))
  let : IsIntegral V.left := inferInstanceAs (IsIntegral (Geometric.SmoothStratum.smoothStratum (Geometric.SupportFiniteType.supportStructureMap B Y.hom)))
  let : LocallyOfFiniteType U.hom := inferInstanceAs
    (LocallyOfFiniteType (Geometric.SmoothStratum.smoothStratumToBase (Geometric.SupportFiniteType.supportStructureMap A X.hom)))
  exact Thom.Scheme.ProductIntegral.Constructions.schemeProduct_isIntegral U V

def productRegularPullbackMap : productRegularScheme X Y A B ⟶ SupportScheme.Constructions.productSupportScheme X Y A B :=
  pullback.map (Geometric.SmoothStratum.smoothStratumToBase (Geometric.SupportFiniteType.supportStructureMap A X.hom))
    (Geometric.SmoothStratum.smoothStratumToBase (Geometric.SupportFiniteType.supportStructureMap B Y.hom))
    (Geometric.SupportFiniteType.supportStructureMap A X.hom) (Geometric.SupportFiniteType.supportStructureMap B Y.hom)
    (Geometric.SmoothStratum.smoothStratumι (Geometric.SupportFiniteType.supportStructureMap A X.hom)) (Geometric.SmoothStratum.smoothStratumι (Geometric.SupportFiniteType.supportStructureMap B Y.hom))
    (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) (Category.comp_id _) (Category.comp_id _)

instance productRegularPullbackMap_open : IsOpenImmersion (productRegularPullbackMap X Y A B) :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance rfl rfl

variable (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (πX : Z ⟶ X) (πY : Z ⟶ Y)
  (hprod : IsLimit (BinaryFan.mk πX πY))

def productRegularSupportMap : productRegularScheme X Y A B ⟶
    Geometric.GenericPoint.reducedSupportScheme (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod) :=
  productRegularPullbackMap X Y A B ≫ (SupportScheme.Constructions.productSupportReducedIso X Y A B Z πX πY hprod).hom

instance productRegularSupportMap_open :
    IsOpenImmersion (productRegularSupportMap X Y A B Z πX πY hprod) := by
  unfold productRegularSupportMap
  infer_instance

@[reassoc]
theorem productRegularSupportMap_base :
    productRegularSupportMap X Y A B Z πX πY hprod ≫
      Geometric.SupportFiniteType.supportStructureMap (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod) Z.hom =
    pullback.fst (Geometric.SmoothStratum.smoothStratumToBase (Geometric.SupportFiniteType.supportStructureMap A X.hom))
      (Geometric.SmoothStratum.smoothStratumToBase (Geometric.SupportFiniteType.supportStructureMap B Y.hom)) ≫
        Geometric.SmoothStratum.smoothStratumToBase (Geometric.SupportFiniteType.supportStructureMap A X.hom) := by
  have hb : (SupportScheme.Constructions.productSupportReducedIso X Y A B Z πX πY hprod).hom ≫
      Geometric.SupportFiniteType.supportStructureMap (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod) Z.hom =
      pullback.fst (Geometric.SupportFiniteType.supportStructureMap A X.hom) (Geometric.SupportFiniteType.supportStructureMap B Y.hom) ≫
        Geometric.SupportFiniteType.supportStructureMap A X.hom := by
    unfold Geometric.SupportFiniteType.supportStructureMap
    rw [SupportScheme.Constructions.productSupportReducedIso_inclusion_assoc, Dimension.productSupportInclusion_base]
    rfl
  unfold productRegularSupportMap
  rw [Category.assoc, hb, ← Category.assoc, productRegularPullbackMap,
    pullback.map, pullback.lift_fst, Category.assoc]
  rfl

instance productRegularSupportMap_smooth_base :
    Smooth (productRegularSupportMap X Y A B Z πX πY hprod ≫
      Geometric.SupportFiniteType.supportStructureMap (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod) Z.hom) := by
  rw [productRegularSupportMap_base]
  have : Smooth (Geometric.SmoothStratum.smoothStratumToBase (Geometric.SupportFiniteType.supportStructureMap A X.hom)) := inferInstance
  have : Smooth (Geometric.SmoothStratum.smoothStratumToBase (Geometric.SupportFiniteType.supportStructureMap B Y.hom)) := inferInstance
  infer_instance

variable [LocallyOfFiniteType Z.hom]

/-- The factorization lands in the native algebraic regular locus. -/
def productRegularToSmoothStratum : productRegularScheme X Y A B ⟶
    Geometric.SmoothStratum.smoothStratum (Geometric.SupportFiniteType.supportStructureMap (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod) Z.hom) :=
  SmoothOpen.openSmoothStratumLift (productRegularSupportMap X Y A B Z πX πY hprod)
    (Geometric.SupportFiniteType.supportStructureMap (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod) Z.hom)

instance productRegularToSmoothStratum_open :
    IsOpenImmersion (productRegularToSmoothStratum X Y A B Z πX πY hprod) := by
  unfold productRegularToSmoothStratum
  infer_instance

@[reassoc]
theorem productRegularToSmoothStratum_inclusion :
    productRegularToSmoothStratum X Y A B Z πX πY hprod ≫
      Geometric.SmoothStratum.smoothStratumι (Geometric.SupportFiniteType.supportStructureMap (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod) Z.hom) =
        productRegularSupportMap X Y A B Z πX πY hprod :=
  SmoothOpen.openSmoothStratumLift_inclusion _ _

theorem productRegularToSmoothStratum_denseRange :
    DenseRange (productRegularToSmoothStratum X Y A B Z πX πY hprod) :=
  (productRegularToSmoothStratum X Y A B Z πX πY hprod).isOpenMap.denseRange_of_isPreirreducibleSpace _

end AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.RegularStratum

end

end OAI
