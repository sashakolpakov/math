import OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.SupportDimension

/-! # Support Projections -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.SupportProjections.BundleCycles

noncomputable section

/-! The product projections on the actual reduced inverse-image support
commute with its closed inclusion in the original ambient product. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (B : IrreducibleCloseds Y.left)
    (Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (πX : Z ⟶ X) (πY : Z ⟶ Y)
    (hprod : IsLimit (BinaryFan.mk πX πY)) [LocallyOfFiniteType Z.hom]

omit [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom] in
theorem projectionSupportReducedOverIso_fst :
    (SupportDimension.BundleCycles.projectionSupportReducedOverIso X Y B Z πX πY hprod).hom ≫
      (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient Z (ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod) ≫ πX) =
      SupportDimension.BundleCycles.projectionSupportProductFst X Y B := by
  apply Over.OverMorphism.ext
  change (ReducedSupport.BundleCycles.projectionSupportReducedIso X Y B Z πX πY hprod).hom ≫
    (CycleClass.Geometric.GenericPoint.reducedSupportι (ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod) ≫ πX.left) = _
  rw [← Category.assoc, ReducedSupport.BundleCycles.projectionSupportReducedIso_inclusion]
  exact SupportDimension.BundleCycles.projectionSupportMap_fst X Y B Z πX πY hprod

omit [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom] in
theorem projectionSupportReducedOverIso_snd :
    (SupportDimension.BundleCycles.projectionSupportReducedOverIso X Y B Z πX πY hprod).hom ≫
      (CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient Z (ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod) ≫ πY) =
      SupportDimension.BundleCycles.projectionSupportProductSnd X Y B ≫ CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient Y B := by
  apply Over.OverMorphism.ext
  change (ReducedSupport.BundleCycles.projectionSupportReducedIso X Y B Z πX πY hprod).hom ≫
    (CycleClass.Geometric.GenericPoint.reducedSupportι (ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod) ≫ πY.left) = _
  rw [← Category.assoc, ReducedSupport.BundleCycles.projectionSupportReducedIso_inclusion]
  exact SupportDimension.BundleCycles.projectionSupportMap_snd X Y B Z πX πY hprod

omit [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom] in
theorem projectionReducedFst_inclusion :
    SupportDimension.BundleCycles.projectionReducedFst X Y B Z πX πY hprod =
      CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient Z (ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod) ≫ πX := by
  apply (cancel_epi (SupportDimension.BundleCycles.projectionSupportReducedOverIso X Y B Z πX πY hprod).hom).mp
  exact ((SupportDimension.BundleCycles.projectionSupportReducedOverIso X Y B Z πX πY hprod).hom_inv_id_assoc _).trans
    (projectionSupportReducedOverIso_fst X Y B Z πX πY hprod).symm

omit [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom] in
theorem projectionReducedSnd_inclusion :
    SupportDimension.BundleCycles.projectionReducedSnd X Y B Z πX πY hprod ≫ CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient Y B =
      CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient Z (ReducedSupport.BundleCycles.projectionIrreducibleSupport X Y B Z πX πY hprod) ≫ πY := by
  apply (cancel_epi (SupportDimension.BundleCycles.projectionSupportReducedOverIso X Y B Z πX πY hprod).hom).mp
  change _ ≫ ((_ ≫ SupportDimension.BundleCycles.projectionSupportProductSnd X Y B) ≫ CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient Y B) = _
  rw [Category.assoc (SupportDimension.BundleCycles.projectionSupportReducedOverIso X Y B Z πX πY hprod).inv]
  exact ((SupportDimension.BundleCycles.projectionSupportReducedOverIso X Y B Z πX πY hprod).hom_inv_id_assoc _).trans
    (projectionSupportReducedOverIso_snd X Y B Z πX πY hprod).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.SupportProjections.BundleCycles
