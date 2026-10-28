import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.PresheafUnit

/-! # Unit Augmentation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.UnitAugmentation.IntrinsicCechPresheafUnit

noncomputable section

/-! The actual native Čech augmentation is the presheaf augmentation under the canonical sheafification unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
  (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))

theorem singleIso_zero :
    (((Functor.IntrinsicCechFunctor.singleIso R X).hom.app F).f 0).hom =
      toSheafify (Opens.grothendieckTopology X) F.obj := by
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem augmentation :
    AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.augmentation R X U F.obj ≫ (PresheafUnit.IntrinsicCechPresheafUnit.iso R X U F).hom =
      (HomologicalComplex.singleMapHomologicalComplex
        (sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) (.up ℕ) 0).inv.app F ≫
      ((sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).map
        ((Functor.IntrinsicCechFunctor.sheafAugmentation R X U).app F) := by
  apply HomologicalComplex.from_single_hom_ext
  let a := (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.augmentation R X U F.obj).f 0
  change a ≫ toSheafify (Opens.grothendieckTopology X) _ =
    𝟙 _ ≫ ((((Functor.IntrinsicCechFunctor.singleIso R X).hom.app F).f 0).hom ≫
      sheafifyMap (Opens.grothendieckTopology X) a)
  exact (toSheafify_naturality (Opens.grothendieckTopology X) a).trans
    ((congrArg (fun k => k ≫ sheafifyMap (Opens.grothendieckTopology X) a)
      (singleIso_zero R X F).symm).trans (Category.id_comp _).symm)

theorem augmentation_zero :
    (((Functor.IntrinsicCechFunctor.sheafAugmentation R X U).app F).f 0).hom =
      (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.augmentation R X U F.obj).f 0 ≫ (PresheafUnit.IntrinsicCechPresheafUnit.iso R X U F).hom.f 0 := by
  let a := (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.augmentation R X U F.obj).f 0
  change (((Functor.IntrinsicCechFunctor.singleIso R X).hom.app F).f 0).hom ≫
      sheafifyMap (Opens.grothendieckTopology X) a = a ≫ toSheafify (Opens.grothendieckTopology X) _
  exact (congrArg (fun k => k ≫ sheafifyMap (Opens.grothendieckTopology X) a)
    (singleIso_zero R X F)).trans (toSheafify_naturality (Opens.grothendieckTopology X) a).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.UnitAugmentation.IntrinsicCechPresheafUnit
