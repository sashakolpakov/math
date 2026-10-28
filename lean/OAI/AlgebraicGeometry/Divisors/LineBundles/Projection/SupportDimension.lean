import OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.ReducedSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport

/-! # Support Dimension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.SupportDimension.BundleCycles

noncomputable section

section

/-! The reduced inverse-image support has genuine product projections
over the complex base. Their universal property follows from its actual
scheme isomorphism with the fiber product. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.Dimension
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (B : IrreducibleCloseds Y.left)
    (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (πX : Z ⟶ X) (πY : Z ⟶ Y)
    (hprod : IsLimit (BinaryFan.mk πX πY))

omit [AlgebraicGeometry.IsIntegral X.left] [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] in
theorem projectionSupportMap_fst :
    ReducedSupport.BundleCycles.projectionSupportMap X Y B Z πX πY hprod ≫ πX.left =
      pullback.fst X.hom (CycleClass.Geometric.SupportFiniteType.supportStructureMap B Y.hom) := by
  let e := CycleClass.Thom.Product.SupportScheme.Constructions.productPresentationIso X Y Z πX πY hprod
  have he : e.inv ≫ πX.left = pullback.fst X.hom Y.hom := by
    rw [← CycleClass.Thom.Product.SupportScheme.Constructions.productPresentationIso_hom_fst X Y Z πX πY hprod]
    exact e.inv_hom_id_assoc _
  change (ReducedSupport.BundleCycles.projectionSupportPullbackMap X Y B ≫ e.inv) ≫ πX.left = _
  rw [Category.assoc, he]
  change pullback.lift _ _ _ ≫ pullback.fst X.hom Y.hom = _
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

omit [AlgebraicGeometry.IsIntegral X.left] [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] in
theorem projectionSupportMap_snd :
    ReducedSupport.BundleCycles.projectionSupportMap X Y B Z πX πY hprod ≫ πY.left =
      pullback.snd X.hom (CycleClass.Geometric.SupportFiniteType.supportStructureMap B Y.hom) ≫ CycleClass.Geometric.GenericPoint.reducedSupportι B := by
  let e := CycleClass.Thom.Product.SupportScheme.Constructions.productPresentationIso X Y Z πX πY hprod
  have he : e.inv ≫ πY.left = pullback.snd X.hom Y.hom := by
    rw [← CycleClass.Thom.Product.SupportScheme.Constructions.productPresentationIso_hom_snd X Y Z πX πY hprod]
    exact e.inv_hom_id_assoc _
  change (ReducedSupport.BundleCycles.projectionSupportPullbackMap X Y B ≫ e.inv) ≫ πY.left = _
  rw [Category.assoc, he]
  exact pullback.lift_snd _ _ _

omit [AlgebraicGeometry.IsIntegral X.left] [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] in
theorem projectionSupportMap_base :
    ReducedSupport.BundleCycles.projectionSupportMap X Y B Z πX πY hprod ≫ Z.hom =
      pullback.fst X.hom (CycleClass.Geometric.SupportFiniteType.supportStructureMap B Y.hom) ≫ X.hom := by
  rw [← πX.w, ← Category.assoc, projectionSupportMap_fst]
  rfl

def projectionSupportProductOver : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (pullback.fst X.hom (CycleClass.Geometric.SupportFiniteType.supportStructureMap B Y.hom) ≫ X.hom)

def projectionSupportProductFst : projectionSupportProductOver X Y B ⟶ X :=
  Over.homMk (pullback.fst X.hom (CycleClass.Geometric.SupportFiniteType.supportStructureMap B Y.hom)) rfl

def projectionSupportProductSnd : projectionSupportProductOver X Y B ⟶ CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y B :=
  Over.homMk (pullback.snd X.hom (CycleClass.Geometric.SupportFiniteType.supportStructureMap B Y.hom)) pullback.condition.symm

def projectionSupportProductIsLimit : IsLimit (BinaryFan.mk
    (projectionSupportProductFst X Y B) (projectionSupportProductSnd X Y B)) :=
  (pullbackIsPullback X.hom (CycleClass.Geometric.SupportFiniteType.supportStructureMap B Y.hom)).pullbackConeEquivBinaryFanFunctor

variable [LocallyOfFiniteType Z.hom]

def projectionSupportReducedOverIso : projectionSupportProductOver X Y B ≅
    CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Z (ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod) :=
  Over.isoMk (ReducedSupport.BundleCycles.projectionSupportReducedIso X Y B Z πX πY hprod) (by
    change (ReducedSupport.BundleCycles.projectionSupportReducedIso X Y B Z πX πY hprod).hom ≫
      (CycleClass.Geometric.GenericPoint.reducedSupportι (ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod) ≫ Z.hom) = _
    rw [← Category.assoc, ReducedSupport.BundleCycles.projectionSupportReducedIso_inclusion, projectionSupportMap_base]
    rfl)

def projectionReducedFst : CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Z (ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod) ⟶ X :=
  (projectionSupportReducedOverIso X Y B Z πX πY hprod).inv ≫ projectionSupportProductFst X Y B

def projectionReducedSnd : CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Z (ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod) ⟶ CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y B :=
  (projectionSupportReducedOverIso X Y B Z πX πY hprod).inv ≫ projectionSupportProductSnd X Y B

def projectionReducedIsLimit : IsLimit (BinaryFan.mk
    (projectionReducedFst X Y B Z πX πY hprod) (projectionReducedSnd X Y B Z πX πY hprod)) :=
  IsLimit.ofIsoLimit (projectionSupportProductIsLimit X Y B)
    (BinaryFan.ext (projectionSupportReducedOverIso X Y B Z πX πY hprod)
      ((projectionSupportReducedOverIso X Y B Z πX πY hprod).hom_inv_id_assoc
        (projectionSupportProductFst X Y B)).symm
      ((projectionSupportReducedOverIso X Y B Z πX πY hprod).hom_inv_id_assoc
        (projectionSupportProductSnd X Y B)).symm)

end

/-! Dimensions and codimensions of the actual projection inverse-image
support are transported through its constructed product isomorphism. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProductDimension.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.Dimension

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (B : IrreducibleCloseds Y.left)
    (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (πX : Z ⟶ X) (πY : Z ⟶ Y)
    (hprod : IsLimit (BinaryFan.mk πX πY)) [LocallyOfFiniteType Z.hom]

omit [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom] in
theorem projectionSupportReducedIso_base :
    (ReducedSupport.BundleCycles.projectionSupportReducedIso X Y B Z πX πY hprod).hom ≫
      CycleClass.Geometric.SupportFiniteType.supportStructureMap (ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod) Z.hom =
      pullback.fst X.hom (CycleClass.Geometric.SupportFiniteType.supportStructureMap B Y.hom) ≫ X.hom := by
  change (ReducedSupport.BundleCycles.projectionSupportReducedIso X Y B Z πX πY hprod).hom ≫
    (CycleClass.Geometric.GenericPoint.reducedSupportι (ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod) ≫ Z.hom) = _
  rw [← Category.assoc, ReducedSupport.BundleCycles.projectionSupportReducedIso_inclusion, projectionSupportMap_base]

omit [LocallyOfFiniteType Z.hom] in
theorem projectionIrreducibleSupport_dimension :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod) Z.hom =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom + Foundations.Scheme.SupportDimension.supportTranscendenceDimension B Y.hom := by
  let YB := CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y B
  let : IsIntegral YB.left := CycleClass.Geometric.GenericPoint.reducedSupportScheme_isIntegral B
  let : LocallyOfFiniteType YB.hom := CycleClass.Geometric.SupportFiniteType.supportStructureMap_locallyOfFiniteType B Y.hom
  have h := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion
    (ReducedSupport.BundleCycles.projectionSupportReducedIso X Y B Z πX πY hprod).hom
    (CycleClass.Geometric.SupportFiniteType.supportStructureMap (ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod) Z.hom)
  rw [projectionSupportReducedIso_base] at h
  exact h.symm.trans (CycleClass.Thom.Scheme.ProductDimension.Constructions.schemeProduct_dimension X YB)

include hprod in
omit [LocallyOfFiniteType Z.hom] in
theorem productPresentation_dimension [IsIntegral Y.left] [IsIntegral Z.left] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Z.hom = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom + Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom := by
  let := CycleClass.Thom.Scheme.ProductIntegral.Constructions.schemeProduct_isIntegral X Y
  let e := CycleClass.Thom.Product.SupportScheme.Constructions.productPresentationIso X Y Z πX πY hprod
  have hb : e.inv ≫ Z.hom = pullback.fst X.hom Y.hom ≫ X.hom := by
    rw [← CycleClass.Thom.Product.SupportTo.Constructions.Dimension.productPresentationIso_base X Y Z πX πY hprod]
    exact e.inv_hom_id_assoc _
  have h := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion e.inv Z.hom
  rw [hb] at h
  exact h.symm.trans (CycleClass.Thom.Scheme.ProductDimension.Constructions.schemeProduct_dimension X Y)

omit [LocallyOfFiniteType Z.hom] in
theorem projectionIrreducibleSupport_codimension [IsIntegral Y.left] [IsIntegral Z.left]
    (p : ℕ) (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B Y.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod) Z.hom + p =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Z.hom := by
  rw [projectionIrreducibleSupport_dimension, productPresentation_dimension X Y Z πX πY hprod, Nat.add_assoc, hp]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.SupportDimension.BundleCycles
