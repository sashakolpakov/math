import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LiteralCechPullback
import OAI.AlgebraicGeometry.Comparison.Betti.Cech.PullbackGlobalIsomorphism

/-! # Literal Cech Pullback Classes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LiteralCechPullbackClasses

noncomputable section

section

/-! The literal sectionwise pullback is exactly the established map
of native additive Čech complexes in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open OAI.AlgebraicGeometry.Comparison.Betti.Cech.PullbackGlobalIsomorphism

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {I : Type} (U : I → Opens Y)
    (F : TopCat.Sheaf AddCommGrpCat.{0} Y) (G : TopCat.Sheaf AddCommGrpCat.{0} X)
    (a : F.obj ⟶ (Opens.map f).op ⋙ G.obj)

theorem literalCechPullback_native_coordinate (n : ℕ)
    (z : ((CategoryTheory.cechComplexFunctor U).obj F.obj).X n) (t : Fin (n + 1) → I) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates G.obj (fun i => (Opens.map f).obj (U i)) n
        ((Comparison.Betti.Cech.PullbackGlobalIsomorphism.additiveCechPullbackMap f U F G a).f n z) t =
      LiteralCechPullback.literalCechPullback f U F.obj G.obj a n (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F.obj U n z) t := by
  let b := eqToHom (congrArg op (SheafCohomology.Cech.Cochains.TopologicalSpace.Opens.piObj_eq_iInf (fun j => U (t j))))
  let e := Comparison.Betti.AdditiveCechImage.additiveCechDirectImageSectionIso f U G.obj n t
  let p := DivisorClass.Chern.Abelian.CechCoordinates.abelianCechIntersectionIso G.obj (fun i => (Opens.map f).obj (U i)) t
  let q := LiteralCechPullback.literalCechPreimageIso f U G.obj t
  have he : e.hom ≫ p.hom = ((Opens.map f).op ⋙ G.obj).map b ≫ q.hom := by
    change G.obj.map _ ≫ G.obj.map _ = G.obj.map _ ≫ G.obj.map _
    exact (G.obj.map_comp _ _).symm.trans
      ((congrArg G.obj.map (Subsingleton.elim _ _)).trans (G.obj.map_comp _ _))
  have ha := a.naturality b
  have h : (a.app (op (∏ᶜ fun j => U (t j))) ≫ e.hom) ≫ p.hom =
      (F.obj.map b ≫ a.app (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U t))) ≫ q.hom := by
    exact (Category.assoc _ _ _).trans ((congrArg (a.app (op (∏ᶜ fun j => U (t j))) ≫ ·) he).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ q.hom) ha.symm)))
  rw [DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates_apply, Comparison.Betti.Cech.PullbackGlobalIsomorphism.additiveCechPullbackMap_coordinate]
  exact ConcreteCategory.congr_hom h (SheafCohomology.Cech.Cochains.TopologicalSpace.cechCochainAddEquiv F.obj U n z t)

theorem literalCechPullback_native (n : ℕ)
    (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F.obj U n) :
    (Comparison.Betti.Cech.PullbackGlobalIsomorphism.additiveCechPullbackMap f U F G a).f n ((DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F.obj U n).symm k) =
      (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates G.obj (fun i => (Opens.map f).obj (U i)) n).symm
        (LiteralCechPullback.literalCechPullback f U F.obj G.obj a n k) := by
  apply (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates G.obj (fun i => (Opens.map f).obj (U i)) n).injective
  rw [AddEquiv.apply_symm_apply]
  funext t
  rw [literalCechPullback_native_coordinate, AddEquiv.apply_symm_apply]

end

/-! The original sectionwise Čech pullback carries native cocycle
classes to the classes of the explicitly pulled sections. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.Comparison.Betti.Cech.PullbackGlobalIsomorphism OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {I : Type} (U : I → Opens Y)
    (F : TopCat.Sheaf AddCommGrpCat.{0} Y) (G : TopCat.Sheaf AddCommGrpCat.{0} X)
    (a : F.obj ⟶ (Opens.map f).op ⋙ G.obj)

theorem literalCechPullback_nativeClass (n : ℕ) (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain F.obj U (n + 1))
    (hk : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta F.obj U (n + 1) k = 0) :
    HomologicalComplex.homologyMap (Comparison.Betti.Cech.PullbackGlobalIsomorphism.additiveCechPullbackMap f U F G a) (n + 1)
        (DivisorClass.Chern.Abelian.CechClasses.abelianCechNativeClass U F.obj n k hk) =
      DivisorClass.Chern.Abelian.CechClasses.abelianCechNativeClass (fun i => (Opens.map f).obj (U i)) G.obj n
        (LiteralCechPullback.literalCechPullback f U F.obj G.obj a (n + 1) k)
        (LiteralCechPullback.literalCechPullback_closed f U F.obj G.obj a (n + 1) k hk) := by
  let L := (cechComplexFunctor U).obj F.obj
  let V := fun i => (Opens.map f).obj (U i)
  let M := (cechComplexFunctor V).obj G.obj
  let p := Comparison.Betti.Cech.PullbackGlobalIsomorphism.additiveCechPullbackMap f U F G a
  let x := (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates F.obj U (n + 1)).symm k
  have hx := DivisorClass.Chern.Abelian.CechClasses.abelianCechNative_closed U F.obj (n + 1) k hk
  have he := literalCechPullback_native f U F G a (n + 1) k
  have hfx : M.d (n + 1) (n + 2) (p.f (n + 1) x) = 0 :=
    (congrArg (M.d (n + 1) (n + 2)) he).trans
      (DivisorClass.Chern.Abelian.CechClasses.abelianCechNative_closed V G.obj (n + 1) _
        (LiteralCechPullback.literalCechPullback_closed f U F.obj G.obj a (n + 1) k hk))
  unfold DivisorClass.Chern.Abelian.CechClasses.abelianCechNativeClass
  rw [SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.homologyMap_abCyclesMk n p x hx hfx]
  congr 1
  apply (AddCommGrpCat.mono_iff_injective (M.iCycles (n + 1))).mp inferInstance
  rw [SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk, SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk]
  exact he

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LiteralCechPullbackClasses
