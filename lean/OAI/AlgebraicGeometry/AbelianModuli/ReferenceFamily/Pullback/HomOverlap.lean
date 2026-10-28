import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CompositePullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleDescentLocal

/-! # Hom Overlap -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.HomOverlap.CompositePullbackPoints

noncomputable section

/-! Equality of local comparison maps after every base pullback implies
the literal total-space kernel-pair equation used in effective descent. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S Y W : Scheme.{0}} (X : Over S) (u : Y ⟶ S)

def homAlongAt {Z : Over S} (a : W ⟶ Y) (t : W ⟶ S) (w : a ≫ u = t)
    (h : (Over.pullback u).obj X ⟶ (Over.pullback u).obj Z) :
    (Over.pullback t).obj X ⟶ (Over.pullback t).obj Z := by
  subst t
  exact CompositePullback.CompositePullbackPoints.homAlong X u a h

def pointAt (a : W ⟶ Y) (t : W ⟶ S) (w : a ≫ u = t)
    (x : W ⟶ pullback X.hom u) (hx : x ≫ pullback.snd X.hom u = a) : W ⟶ pullback X.hom t := by
  subst t
  exact CompositePullback.CompositePullbackPoints.point X u a x hx

theorem pointAt_fst (a : W ⟶ Y) (t : W ⟶ S) (w : a ≫ u = t)
    (x : W ⟶ pullback X.hom u) (hx : x ≫ pullback.snd X.hom u = a) :
    pointAt X u a t w x hx ≫ pullback.fst X.hom t = x ≫ pullback.fst X.hom u := by
  subst t
  exact CompositePullback.CompositePullbackPoints.point_fst X u a x hx

theorem pointAt_snd (a : W ⟶ Y) (t : W ⟶ S) (w : a ≫ u = t)
    (x : W ⟶ pullback X.hom u) (hx : x ≫ pullback.snd X.hom u = a) :
    pointAt X u a t w x hx ≫ pullback.snd X.hom t = 𝟙 W := by
  subst t
  exact CompositePullback.CompositePullbackPoints.point_snd X u a x hx

theorem pointAt_homAlongAt {Z : Over S} (a : W ⟶ Y) (t : W ⟶ S) (w : a ≫ u = t)
    (h : (Over.pullback u).obj X ⟶ (Over.pullback u).obj Z)
    (x : W ⟶ pullback X.hom u) (hx : x ≫ pullback.snd X.hom u = a) :
    pointAt X u a t w x hx ≫ (homAlongAt X u a t w h).left ≫ pullback.fst Z.hom t =
      x ≫ h.left ≫ pullback.fst Z.hom u := by
  subst t
  exact CompositePullback.CompositePullbackPoints.point_homAlong X u a h x hx

theorem local_point_base (x : W ⟶ pullback X.hom u) :
    (x ≫ pullback.snd X.hom u) ≫ u = (x ≫ pullback.fst X.hom u) ≫ X.hom := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => x ≫ z) (pullback.condition (f := X.hom) (g := u)).symm).trans
      (Category.assoc _ _ _).symm)

theorem pointwise_eq_of_homAlong_eq {Z : Over S}
    (h : (Over.pullback u).obj X ⟶ (Over.pullback u).obj Z)
    (hc : ∀ {V : Scheme.{0}} (a b : V ⟶ Y) (t : V ⟶ S) (ha : a ≫ u = t) (hb : b ≫ u = t),
      homAlongAt X u a t ha h = homAlongAt X u b t hb h)
    (x y : W ⟶ pullback X.hom u) (hxy : x ≫ pullback.fst X.hom u = y ≫ pullback.fst X.hom u) :
    x ≫ h.left ≫ pullback.fst Z.hom u = y ≫ h.left ≫ pullback.fst Z.hom u := by
  let a := x ≫ pullback.snd X.hom u
  let b := y ≫ pullback.snd X.hom u
  let t := (x ≫ pullback.fst X.hom u) ≫ X.hom
  have ha : a ≫ u = t := local_point_base X u x
  have hb : b ≫ u = t := (local_point_base X u y).trans (congrArg (fun z => z ≫ X.hom) hxy.symm)
  have hp : pointAt X u a t ha x rfl = pointAt X u b t hb y rfl := by
    apply pullback.hom_ext
    · exact (pointAt_fst X u a t ha x rfl).trans (hxy.trans (pointAt_fst X u b t hb y rfl).symm)
    · exact (pointAt_snd X u a t ha x rfl).trans (pointAt_snd X u b t hb y rfl).symm
  exact (pointAt_homAlongAt X u a t ha h x rfl).symm.trans
    ((congrArg (fun z => z ≫ (homAlongAt X u a t ha h).left ≫ pullback.fst Z.hom t) hp).trans
      ((congrArg (fun z : (Over.pullback t).obj X ⟶ (Over.pullback t).obj Z =>
        pointAt X u b t hb y rfl ≫ z.left ≫ pullback.fst Z.hom t) (hc a b t ha hb)).trans
          (pointAt_homAlongAt X u b t hb h y rfl)))

theorem compatible_of_homAlong_eq {Z : Over S}
    (h : (Over.pullback u).obj X ⟶ (Over.pullback u).obj Z)
    (hc : ∀ {V : Scheme.{0}} (a b : V ⟶ Y) (t : V ⟶ S) (ha : a ≫ u = t) (hb : b ≫ u = t),
      homAlongAt X u a t ha h = homAlongAt X u b t hb h) : EtaleDescentLocal.EtaleDescent.Compatible u h :=
  pointwise_eq_of_homAlong_eq X u h hc _ _ pullback.condition

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.HomOverlap.CompositePullbackPoints
