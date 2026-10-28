import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportPoints
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportTo

/-! # Support Over Iso -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportOverIso.Constructions

noncomputable section

/-! The actual reduced product support is a limiting product of the two
reduced supports over the complex base, with its genuine induced projections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.Dimension OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportPoints.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) (A : IrreducibleCloseds X.left) (B : IrreducibleCloseds Y.left)

def supportProductOver : Over Foundations.Scheme.ProjectiveSpace.complexBase :=
  Over.mk (pullback.fst (Geometric.SupportFiniteType.supportStructureMap A X.hom) (Geometric.SupportFiniteType.supportStructureMap B Y.hom) ≫
    Geometric.SupportFiniteType.supportStructureMap A X.hom)

def supportProductFst : supportProductOver X Y A B ⟶ SupportPoints.Constructions.supportOver X A :=
  Over.homMk (pullback.fst (Geometric.SupportFiniteType.supportStructureMap A X.hom) (Geometric.SupportFiniteType.supportStructureMap B Y.hom)) rfl

def supportProductSnd : supportProductOver X Y A B ⟶ SupportPoints.Constructions.supportOver Y B :=
  Over.homMk (pullback.snd (Geometric.SupportFiniteType.supportStructureMap A X.hom) (Geometric.SupportFiniteType.supportStructureMap B Y.hom)) pullback.condition.symm

def supportProductIsLimit : IsLimit (BinaryFan.mk (supportProductFst X Y A B) (supportProductSnd X Y A B)) :=
  (pullbackIsPullback (Geometric.SupportFiniteType.supportStructureMap A X.hom) (Geometric.SupportFiniteType.supportStructureMap B Y.hom)).pullbackConeEquivBinaryFanFunctor

variable (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (πX : Z ⟶ X) (πY : Z ⟶ Y)
  (hprod : IsLimit (BinaryFan.mk πX πY)) [LocallyOfFiniteType X.hom]

def productSupportReducedOverIso : supportProductOver X Y A B ≅
    SupportPoints.Constructions.supportOver Z (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod) :=
  Over.isoMk (SupportScheme.Constructions.productSupportReducedIso X Y A B Z πX πY hprod) (by
    change (SupportScheme.Constructions.productSupportReducedIso X Y A B Z πX πY hprod).hom ≫
      (Geometric.GenericPoint.reducedSupportι (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod) ≫ Z.hom) = _
    rw [SupportScheme.Constructions.productSupportReducedIso_inclusion_assoc, SupportTo.Constructions.Dimension.productSupportInclusion_base]
    rfl)

def reducedProductFst : SupportPoints.Constructions.supportOver Z (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod) ⟶ SupportPoints.Constructions.supportOver X A :=
  (productSupportReducedOverIso X Y A B Z πX πY hprod).inv ≫ supportProductFst X Y A B

def reducedProductSnd : SupportPoints.Constructions.supportOver Z (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod) ⟶ SupportPoints.Constructions.supportOver Y B :=
  (productSupportReducedOverIso X Y A B Z πX πY hprod).inv ≫ supportProductSnd X Y A B

def reducedProductIsLimit : IsLimit (BinaryFan.mk
    (reducedProductFst X Y A B Z πX πY hprod) (reducedProductSnd X Y A B Z πX πY hprod)) :=
  IsLimit.ofIsoLimit (supportProductIsLimit X Y A B)
    (BinaryFan.ext (productSupportReducedOverIso X Y A B Z πX πY hprod)
      (by change _ = _ ≫ (_ ≫ _); rw [Iso.hom_inv_id_assoc]; rfl)
      (by change _ = _ ≫ (_ ≫ _); rw [Iso.hom_inv_id_assoc]; rfl))

@[reassoc]
theorem reducedProductFst_inclusion :
    reducedProductFst X Y A B Z πX πY hprod ≫ SupportPoints.Constructions.supportOverInclusion X A =
      SupportPoints.Constructions.supportOverInclusion Z (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod) ≫ πX := by
  have he : (SupportScheme.Constructions.productPresentationIso X Y Z πX πY hprod).inv ≫ πX.left = pullback.fst X.hom Y.hom := by
    rw [← SupportScheme.Constructions.productPresentationIso_hom_fst X Y Z πX πY hprod]
    exact (SupportScheme.Constructions.productPresentationIso X Y Z πX πY hprod).inv_hom_id_assoc _
  have hm : SupportScheme.Constructions.productSupportInclusion X Y A B Z πX πY hprod ≫ πX.left =
      pullback.fst (Geometric.SupportFiniteType.supportStructureMap A X.hom) (Geometric.SupportFiniteType.supportStructureMap B Y.hom) ≫ Geometric.GenericPoint.reducedSupportι A := by
    unfold SupportScheme.Constructions.productSupportInclusion
    rw [Category.assoc, he]
    exact pullback.lift_fst _ _ _
  apply Over.OverMorphism.ext
  apply (cancel_epi (SupportScheme.Constructions.productSupportReducedIso X Y A B Z πX πY hprod).hom).mp
  change (SupportScheme.Constructions.productSupportReducedIso X Y A B Z πX πY hprod).hom ≫
    (((SupportScheme.Constructions.productSupportReducedIso X Y A B Z πX πY hprod).inv ≫
      pullback.fst (Geometric.SupportFiniteType.supportStructureMap A X.hom) (Geometric.SupportFiniteType.supportStructureMap B Y.hom)) ≫ Geometric.GenericPoint.reducedSupportι A) =
    (SupportScheme.Constructions.productSupportReducedIso X Y A B Z πX πY hprod).hom ≫
      (Geometric.GenericPoint.reducedSupportι (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod) ≫ πX.left)
  simp only [Category.assoc, Iso.hom_inv_id_assoc, SupportScheme.Constructions.productSupportReducedIso_inclusion_assoc]
  exact hm.symm

@[reassoc]
theorem reducedProductSnd_inclusion :
    reducedProductSnd X Y A B Z πX πY hprod ≫ SupportPoints.Constructions.supportOverInclusion Y B =
      SupportPoints.Constructions.supportOverInclusion Z (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod) ≫ πY := by
  have he : (SupportScheme.Constructions.productPresentationIso X Y Z πX πY hprod).inv ≫ πY.left = pullback.snd X.hom Y.hom := by
    rw [← SupportScheme.Constructions.productPresentationIso_hom_snd X Y Z πX πY hprod]
    exact (SupportScheme.Constructions.productPresentationIso X Y Z πX πY hprod).inv_hom_id_assoc _
  have hm : SupportScheme.Constructions.productSupportInclusion X Y A B Z πX πY hprod ≫ πY.left =
      pullback.snd (Geometric.SupportFiniteType.supportStructureMap A X.hom) (Geometric.SupportFiniteType.supportStructureMap B Y.hom) ≫ Geometric.GenericPoint.reducedSupportι B := by
    unfold SupportScheme.Constructions.productSupportInclusion
    rw [Category.assoc, he]
    exact pullback.lift_snd _ _ _
  apply Over.OverMorphism.ext
  apply (cancel_epi (SupportScheme.Constructions.productSupportReducedIso X Y A B Z πX πY hprod).hom).mp
  change (SupportScheme.Constructions.productSupportReducedIso X Y A B Z πX πY hprod).hom ≫
    (((SupportScheme.Constructions.productSupportReducedIso X Y A B Z πX πY hprod).inv ≫
      pullback.snd (Geometric.SupportFiniteType.supportStructureMap A X.hom) (Geometric.SupportFiniteType.supportStructureMap B Y.hom)) ≫ Geometric.GenericPoint.reducedSupportι B) =
    (SupportScheme.Constructions.productSupportReducedIso X Y A B Z πX πY hprod).hom ≫
      (Geometric.GenericPoint.reducedSupportι (SupportScheme.Constructions.productIrreducibleSupport X Y A B Z πX πY hprod) ≫ πY.left)
  simp only [Category.assoc, Iso.hom_inv_id_assoc, SupportScheme.Constructions.productSupportReducedIso_inclusion_assoc]
  exact hm.symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportOverIso.Constructions
