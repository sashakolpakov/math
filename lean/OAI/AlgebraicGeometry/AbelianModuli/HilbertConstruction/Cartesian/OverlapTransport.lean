import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackIsoComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.OverIsoNaturality

/-! # Overlap Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.OverlapTransport

noncomputable section

/-! Isomorphisms on an overlap induce compatible transport after every
base change, with the original Cartesian projections retained. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u v w

private theorem conjugateProjection {C : Type v} [Category.{w} C]
    {A B D E F G : C} (a : A ⟶ B) (m : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F)
    (p : D ⟶ F) (q : B ⟶ G) (e : G ⟶ F) (x : A ⟶ G)
    (hc : c ≫ d = p) (hm : m ≫ p = q ≫ e) (ha : a ≫ q = x) :
    (a ≫ m ≫ c) ≫ d = x ≫ e := by
  simp only [Category.assoc, hc]
  rw [hm, ← Category.assoc, ha]

private theorem isoOfSquare {C : Type v} [Category.{w} C]
    {A A' B B' : C} (a : A ≅ A') (b : B ≅ B') (e : A ≅ B) (f : A' ≅ B')
    (h : a.hom ≫ f.hom = e.hom ≫ b.hom) : e = a ≪≫ f ≪≫ b.symm := by
  apply Iso.ext
  apply (cancel_mono b.hom).mp
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id] using h.symm

private def factorOverMap {S T U : Scheme.{u}}
    (c : T ⟶ U) (l : U ⟶ S) (a : T ⟶ S) (h : c ≫ l = a) :
    (Over.mk a : Over S) ⟶ Over.mk l := Over.homMk c h

variable {A B W T U : Scheme.{u}}
variable (F : Over A) (G : Over B) (l : W ⟶ A) (r : W ⟶ B)
variable (e : (Over.pullback l).obj F ≅ (Over.pullback r).obj G)
variable (c : T ⟶ W) (a : T ⟶ A) (b : T ⟶ B)
variable (hl : c ≫ l = a) (hr : c ≫ r = b)

def cartesianOverlapPullbackIso : (Over.pullback a).obj F ≅ (Over.pullback b).obj G :=
  Single.ParameterBaseChange.singleParameterBaseChangeIso (factorOverMap c l a hl) F ≪≫
    (Over.pullback c).mapIso e ≪≫
      (Single.ParameterBaseChange.singleParameterBaseChangeIso (factorOverMap c r b hr) G).symm

theorem cartesianOverlapPullbackIso_square :
    (cartesianOverlapPullbackIso F G l r e c a b hl hr).hom.left ≫
        Single.ParameterBaseChange.singleParameterBaseChangeMap (Over.homMk c hr : Over.mk b ⟶ Over.mk r) G =
      Single.ParameterBaseChange.singleParameterBaseChangeMap (Over.homMk c hl : Over.mk a ⟶ Over.mk l) F ≫
        e.hom.left := by
  let ca := factorOverMap c l a hl
  let cb := factorOverMap c r b hr
  have hp : ((Over.pullback c).map e.hom).left ≫
        pullback.fst ((Over.pullback r).obj G).hom c =
      pullback.fst ((Over.pullback l).obj F).hom c ≫ e.hom.left :=
    pullback.lift_fst _ _ _
  change ((Single.ParameterBaseChange.singleParameterBaseChangeIso ca F).hom.left ≫
      (((Over.pullback c).map e.hom).left ≫
        (Single.ParameterBaseChange.singleParameterBaseChangeIso cb G).inv.left)) ≫
      Single.ParameterBaseChange.singleParameterBaseChangeMap cb G =
    Single.ParameterBaseChange.singleParameterBaseChangeMap ca F ≫ e.hom.left
  exact conjugateProjection (Single.ParameterBaseChange.singleParameterBaseChangeIso ca F).hom.left
    ((Over.pullback c).map e.hom).left (Single.ParameterBaseChange.singleParameterBaseChangeIso cb G).inv.left
    (Single.ParameterBaseChange.singleParameterBaseChangeMap cb G) _ _ e.hom.left (Single.ParameterBaseChange.singleParameterBaseChangeMap ca F)
    (Single.ParameterFunctoriality.singleParameterBaseChangeIso_inv_comp cb G) hp
    (Single.ParameterFunctoriality.singleParameterBaseChangeIso_hom_fst ca F)

variable (u : U ⟶ T)
variable (hl' : (u ≫ c) ≫ l = u ≫ a) (hr' : (u ≫ c) ≫ r = u ≫ b)

theorem cartesianOverlapPullbackIso_natural :
    Single.ParameterBaseChange.singleParameterBaseChangeMap
        (Over.homMk u rfl : Over.mk (u ≫ a) ⟶ Over.mk a) F ≫
        (cartesianOverlapPullbackIso F G l r e c a b hl hr).hom.left =
      (cartesianOverlapPullbackIso F G l r e (u ≫ c) (u ≫ a) (u ≫ b) hl' hr').hom.left ≫
        Single.ParameterBaseChange.singleParameterBaseChangeMap
          (Over.homMk u rfl : Over.mk (u ≫ b) ⟶ Over.mk b) G := by
  let ca := factorOverMap c l a hl
  let cb := factorOverMap c r b hr
  let ua := factorOverMap u a (u ≫ a) rfl
  let ub := factorOverMap u b (u ≫ b) rfl
  let ca' := factorOverMap (u ≫ c) l (u ≫ a) hl'
  let cb' := factorOverMap (u ≫ c) r (u ≫ b) hr'
  let eT := cartesianOverlapPullbackIso F G l r e c a b hl hr
  let eU := cartesianOverlapPullbackIso F G l r e (u ≫ c) (u ≫ a) (u ≫ b) hl' hr'
  have ha : ua ≫ ca = ca' := by
    apply Over.OverMorphism.ext
    rfl
  have hb : ub ≫ cb = cb' := by
    apply Over.OverMorphism.ext
    rfl
  have heT : eT.hom.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap cb G =
      Single.ParameterBaseChange.singleParameterBaseChangeMap ca F ≫ e.hom.left :=
    cartesianOverlapPullbackIso_square F G l r e c a b hl hr
  have heU : eU.hom.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap cb' G =
      Single.ParameterBaseChange.singleParameterBaseChangeMap ca' F ≫ e.hom.left :=
    cartesianOverlapPullbackIso_square F G l r e (u ≫ c) (u ≫ a) (u ≫ b) hl' hr'
  have hua : Single.ParameterBaseChange.singleParameterBaseChangeMap ua F ≫ ((Over.pullback a).obj F).hom =
      ((Over.pullback (u ≫ a)).obj F).hom ≫ u := Single.ParameterFunctoriality.singleParameterBaseChangeMap_over ua F
  have hub : Single.ParameterBaseChange.singleParameterBaseChangeMap ub G ≫ ((Over.pullback b).obj G).hom =
      ((Over.pullback (u ≫ b)).obj G).hom ≫ u := Single.ParameterFunctoriality.singleParameterBaseChangeMap_over ub G
  change Single.ParameterBaseChange.singleParameterBaseChangeMap ua F ≫ eT.hom.left =
    eU.hom.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap ub G
  apply (Single.ParameterBaseChange.singleParameterBaseChangeMap_isPullback cb G).hom_ext
  · calc
      _ = Single.ParameterBaseChange.singleParameterBaseChangeMap ua F ≫
          Single.ParameterBaseChange.singleParameterBaseChangeMap ca F ≫ e.hom.left := by
        rw [Category.assoc, heT]
      _ = Single.ParameterBaseChange.singleParameterBaseChangeMap ca' F ≫ e.hom.left := by
        rw [← Category.assoc, ← Single.ParameterFunctoriality.singleParameterBaseChangeMap_composition, ha]
      _ = eU.hom.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap cb' G := heU.symm
      _ = _ := by
        rw [← hb, Single.ParameterFunctoriality.singleParameterBaseChangeMap_composition, Category.assoc]
  · change (Single.ParameterBaseChange.singleParameterBaseChangeMap ua F ≫ eT.hom.left) ≫
        ((Over.pullback b).obj G).hom =
      (eU.hom.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap ub G) ≫
        ((Over.pullback b).obj G).hom
    calc
      _ = ((Over.pullback (u ≫ a)).obj F).hom ≫ u := by
        rw [Category.assoc, eT.hom.w]
        exact hua
      _ = (eU.hom.left ≫ ((Over.pullback (u ≫ b)).obj G).hom) ≫ u := by
        rw [eU.hom.w]
      _ = _ := by
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun k => eU.hom.left ≫ k) hub.symm).trans (Category.assoc _ _ _).symm)

theorem cartesianOverlapPullbackIso_baseChange :
    cartesianOverlapPullbackIso F G l r e (u ≫ c) (u ≫ a) (u ≫ b) hl' hr' =
      Single.ParameterBaseChange.singleParameterBaseChangeIso
          (Over.homMk u rfl : Over.mk (u ≫ a) ⟶ Over.mk a) F ≪≫
        (Over.pullback u).mapIso (cartesianOverlapPullbackIso F G l r e c a b hl hr) ≪≫
          (Single.ParameterBaseChange.singleParameterBaseChangeIso
            (Over.homMk u rfl : Over.mk (u ≫ b) ⟶ Over.mk b) G).symm := by
  let ua : Over.mk (u ≫ a) ⟶ Over.mk a := Over.homMk u rfl
  let ub : Over.mk (u ≫ b) ⟶ Over.mk b := Over.homMk u rfl
  let eT := cartesianOverlapPullbackIso F G l r e c a b hl hr
  let eU := cartesianOverlapPullbackIso F G l r e (u ≫ c) (u ≫ a) (u ≫ b) hl' hr'
  let ia := Single.ParameterBaseChange.singleParameterBaseChangeIso ua F
  let ib := Single.ParameterBaseChange.singleParameterBaseChangeIso ub G
  have hn := OverIsoNaturality.cartesianAmbientOverIso_natural u
    (Single.ParameterBaseChange.singleParameterBaseChangeMap ua F) (Single.ParameterBaseChange.singleParameterBaseChangeMap ub G)
    (Single.ParameterBaseChange.singleParameterBaseChangeMap_isPullback ua F)
    (Single.ParameterBaseChange.singleParameterBaseChangeMap_isPullback ub G)
    eU.hom eT.hom
    (cartesianOverlapPullbackIso_natural F G l r e c a b hl hr u hl' hr')
  change ia.hom ≫ (Over.pullback u).map eT.hom = eU.hom ≫ ib.hom at hn
  change eU = ia ≪≫ (Over.pullback u).mapIso eT ≪≫ ib.symm
  exact isoOfSquare ia ib eU ((Over.pullback u).mapIso eT) hn

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.OverlapTransport
