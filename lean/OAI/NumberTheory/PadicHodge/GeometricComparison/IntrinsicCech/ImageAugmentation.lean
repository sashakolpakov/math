import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ImageNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.UnitAugmentation
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.ImageAugmentation

/-! # Image Augmentation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ImageAugmentation.IntrinsicCechImage

noncomputable section

/-! The native sheaf Čech direct-image comparison preserves the actual sheaf augmentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem unit_conjugation {C : Type*} [Category* C] {A B B' D D' : C}
    (u : B ≅ B') (v : D ≅ D') (e : B ⟶ D) (a : A ⟶ B) (b : A ⟶ D) (h : a ≫ e = b) :
    (a ≫ u.hom) ≫ (u.inv ≫ e ≫ v.hom) = b ≫ v.hom := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ v.hom) h)

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y)
  {ι : Type} (U : ι → Y.left.Opens) (F : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X)

theorem augmentation :
    (Functor.IntrinsicCechFunctor.sheafAugmentation R Y.left U).app ((DeRham.Int.directImage f).obj F) ≫ (Image.IntrinsicCechImage.iso f U F).hom =
      (HomologicalComplex.singleMapHomologicalComplex (DeRham.Int.directImage f) (.up ℕ) 0).inv.app F ≫
        ((DeRham.Int.directImage f).mapHomologicalComplex (.up ℕ)).map
          ((Functor.IntrinsicCechFunctor.sheafAugmentation R X.left (fun i => f.left ⁻¹ᵁ U i)).app F) := by
  apply HomologicalComplex.from_single_hom_ext
  apply (sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{0} R)).map_injective
  let V := fun i => f.left ⁻¹ᵁ U i
  let G := Cech.Image.CechImage.functor R f.left
  let TY := HomologicalComplex.eval (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R Y.left) (.up ℕ) 0
  let TX := HomologicalComplex.eval (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X.left) (.up ℕ) 0
  let u := TY.mapIso (PresheafUnit.IntrinsicCechPresheafUnit.iso R Y.left U ((DeRham.Int.directImage f).obj F))
  let v := TX.mapIso (PresheafUnit.IntrinsicCechPresheafUnit.iso R X.left V F)
  let e := TY.mapIso (Cech.Image.CechImage.complexIso R f.left U F.obj)
  let a := (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.augmentation R Y.left U (G.obj F.obj)).f 0
  let b := (AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.augmentation R X.left V F.obj).f 0
  let s := (((Functor.IntrinsicCechFunctor.sheafAugmentation R Y.left U).app ((DeRham.Int.directImage f).obj F)).f 0).hom
  let t := (((Functor.IntrinsicCechFunctor.sheafAugmentation R X.left V).app F).f 0).hom
  let m := ((Image.IntrinsicCechImage.iso f U F).hom.f 0).hom
  have hs : s = a ≫ u.hom := UnitAugmentation.IntrinsicCechPresheafUnit.augmentation_zero R Y.left U ((DeRham.Int.directImage f).obj F)
  have ht : t = b ≫ v.hom := UnitAugmentation.IntrinsicCechPresheafUnit.augmentation_zero R X.left V F
  have hm : m = u.inv ≫ e.hom ≫ G.map v.hom := congrArg (fun k => k.f 0) (ImageNaturality.IntrinsicCechImage.map_iso_hom f U F)
  have hc : a ≫ e.hom = G.map b :=
    (congrArg (fun k => k.f 0) (Cech.ImageAugmentation.CechImage.augmentation R f.left U F.obj)).trans (Category.id_comp _)
  change s ≫ m = 𝟙 _ ≫ G.map t
  exact (congrArg (fun k => k ≫ m) hs).trans
    ((congrArg (fun k => (a ≫ u.hom) ≫ k) hm).trans
      ((unit_conjugation u (G.mapIso v) e.hom a (G.map b) hc).trans
        ((G.map_comp b v.hom).symm.trans ((congrArg G.map ht.symm).trans (Category.id_comp _).symm))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ImageAugmentation.IntrinsicCechImage
