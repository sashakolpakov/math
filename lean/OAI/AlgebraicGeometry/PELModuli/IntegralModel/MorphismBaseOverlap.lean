import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.HomOverlap

/-! # Morphism Base Overlap -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.PELModuli.IntegralModel.MorphismBaseOverlap.CompositePullbackTestPoints

/-! Actual points over an arbitrary test scheme in a composite family
pullback. The test scheme need not be reduced or noetherian. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.HomOverlap.CompositePullbackPoints
variable {S Y W V : Scheme.{0}} (X : Over S) (u : Y ⟶ S) (a : W ⟶ Y)

def point (k : V ⟶ W) (x : V ⟶ pullback X.hom u)
    (hx : x ≫ pullback.snd X.hom u = k ≫ a) : V ⟶ pullback X.hom (a ≫ u) :=
  pullback.lift x k hx ≫ (AbelianModuli.ReferenceFamily.CompositePullback.CompositePullbackPoints.comparison X u a).inv

theorem point_fst (k : V ⟶ W) (x : V ⟶ pullback X.hom u)
    (hx : x ≫ pullback.snd X.hom u = k ≫ a) :
    point X u a k x hx ≫ pullback.fst X.hom (a ≫ u) = x ≫ pullback.fst X.hom u := by
  unfold point
  rw [Category.assoc, AbelianModuli.ReferenceFamily.CompositePullback.CompositePullbackPoints.comparison_inv_fst, pullback.lift_fst_assoc]

theorem point_snd (k : V ⟶ W) (x : V ⟶ pullback X.hom u)
    (hx : x ≫ pullback.snd X.hom u = k ≫ a) :
    point X u a k x hx ≫ pullback.snd X.hom (a ≫ u) = k := by
  unfold point
  rw [Category.assoc]
  have h := ((Over.pullbackComp a u).inv.app X).w
  exact (congrArg (fun f => pullback.lift x k hx ≫ f) h).trans (pullback.lift_snd _ _ _)

theorem point_homAlong {Z : Over S}
    (h : (Over.pullback u).obj X ⟶ (Over.pullback u).obj Z)
    (k : V ⟶ W) (x : V ⟶ pullback X.hom u)
    (hx : x ≫ pullback.snd X.hom u = k ≫ a) :
    point X u a k x hx ≫ (AbelianModuli.ReferenceFamily.CompositePullback.CompositePullbackPoints.homAlong X u a h).left ≫ pullback.fst Z.hom (a ≫ u) =
      x ≫ h.left ≫ pullback.fst Z.hom u := by
  let l := pullback.lift x k hx
  let m := ((Over.pullback a).map h).left
  have hm : m ≫ pullback.fst (pullback.snd Z.hom u) a =
      pullback.fst (pullback.snd X.hom u) a ≫ h.left := AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst h a
  change (l ≫ (AbelianModuli.ReferenceFamily.CompositePullback.CompositePullbackPoints.comparison X u a).inv) ≫
    ((AbelianModuli.ReferenceFamily.CompositePullback.CompositePullbackPoints.comparison X u a).hom ≫ m ≫ (AbelianModuli.ReferenceFamily.CompositePullback.CompositePullbackPoints.comparison Z u a).inv) ≫ _ = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [AbelianModuli.ReferenceFamily.CompositePullback.CompositePullbackPoints.comparison_inv_fst, ← Category.assoc m, hm]
  simp only [l, Category.assoc, pullback.lift_fst_assoc]

def pointAt (t : W ⟶ S) (w : a ≫ u = t) (k : V ⟶ W)
    (x : V ⟶ pullback X.hom u) (hx : x ≫ pullback.snd X.hom u = k ≫ a) :
    V ⟶ pullback X.hom t := by
  subst t
  exact point X u a k x hx

theorem pointAt_fst (t : W ⟶ S) (w : a ≫ u = t) (k : V ⟶ W)
    (x : V ⟶ pullback X.hom u) (hx : x ≫ pullback.snd X.hom u = k ≫ a) :
    pointAt X u a t w k x hx ≫ pullback.fst X.hom t = x ≫ pullback.fst X.hom u := by
  subst t
  exact point_fst X u a k x hx

theorem pointAt_snd (t : W ⟶ S) (w : a ≫ u = t) (k : V ⟶ W)
    (x : V ⟶ pullback X.hom u) (hx : x ≫ pullback.snd X.hom u = k ≫ a) :
    pointAt X u a t w k x hx ≫ pullback.snd X.hom t = k := by
  subst t
  exact point_snd X u a k x hx

theorem pointAt_homAlongAt {Z : Over S} (t : W ⟶ S) (w : a ≫ u = t)
    (h : (Over.pullback u).obj X ⟶ (Over.pullback u).obj Z)
    (k : V ⟶ W) (x : V ⟶ pullback X.hom u)
    (hx : x ≫ pullback.snd X.hom u = k ≫ a) :
    pointAt X u a t w k x hx ≫ (AbelianModuli.ReferenceFamily.Pullback.HomOverlap.CompositePullbackPoints.homAlongAt X u a t w h).left ≫ pullback.fst Z.hom t =
      x ≫ h.left ≫ pullback.fst Z.hom u := by
  subst t
  exact point_homAlong X u a h k x hx

end AlgebraicGeometry.PELModuli.IntegralModel.MorphismBaseOverlap.CompositePullbackTestPoints

namespace AlgebraicGeometry.PELModuli.IntegralModel.MorphismBaseOverlap

/-! Equality of the two family maps on the actual base kernel pair
implies the total-space overlap equation required by effective descent.
No condition is imposed on total-space test schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.HomOverlap.CompositePullbackPoints
variable {S Y W : Scheme.{0}} (X : Over S) (u : Y ⟶ S) {Z : Over S}

theorem pointwise_eq_of_base_overlap
    (h : (Over.pullback u).obj X ⟶ (Over.pullback u).obj Z)
    (hc : AbelianModuli.ReferenceFamily.Pullback.HomOverlap.CompositePullbackPoints.homAlongAt X u (pullback.fst u u) (pullback.fst u u ≫ u) rfl h =
      AbelianModuli.ReferenceFamily.Pullback.HomOverlap.CompositePullbackPoints.homAlongAt X u (pullback.snd u u) (pullback.fst u u ≫ u) pullback.condition.symm h)
    (x y : W ⟶ pullback X.hom u)
    (hxy : x ≫ pullback.fst X.hom u = y ≫ pullback.fst X.hom u) :
    x ≫ h.left ≫ pullback.fst Z.hom u = y ≫ h.left ≫ pullback.fst Z.hom u := by
  let a := pullback.fst u u
  let b := pullback.snd u u
  let t := a ≫ u
  have hw : (x ≫ pullback.snd X.hom u) ≫ u = (y ≫ pullback.snd X.hom u) ≫ u :=
    (AbelianModuli.ReferenceFamily.Pullback.HomOverlap.CompositePullbackPoints.local_point_base X u x).trans
      ((congrArg (fun k => k ≫ X.hom) hxy).trans (AbelianModuli.ReferenceFamily.Pullback.HomOverlap.CompositePullbackPoints.local_point_base X u y).symm)
  let k := pullback.lift (x ≫ pullback.snd X.hom u) (y ≫ pullback.snd X.hom u) hw
  have hx : x ≫ pullback.snd X.hom u = k ≫ a := (pullback.lift_fst _ _ _).symm
  have hy : y ≫ pullback.snd X.hom u = k ≫ b := (pullback.lift_snd _ _ _).symm
  let p := CompositePullbackTestPoints.pointAt X u a t rfl k x hx
  let q := CompositePullbackTestPoints.pointAt X u b t pullback.condition.symm k y hy
  have hpq : p = q := by
    apply pullback.hom_ext
    · exact (CompositePullbackTestPoints.pointAt_fst X u a t rfl k x hx).trans
        (hxy.trans (CompositePullbackTestPoints.pointAt_fst X u b t pullback.condition.symm k y hy).symm)
    · exact (CompositePullbackTestPoints.pointAt_snd X u a t rfl k x hx).trans
        (CompositePullbackTestPoints.pointAt_snd X u b t pullback.condition.symm k y hy).symm
  have hp := CompositePullbackTestPoints.pointAt_homAlongAt X u a t rfl h k x hx
  have hq := CompositePullbackTestPoints.pointAt_homAlongAt X u b t pullback.condition.symm h k y hy
  exact hp.symm.trans
    ((congrArg (fun p => p ≫ (AbelianModuli.ReferenceFamily.Pullback.HomOverlap.CompositePullbackPoints.homAlongAt X u a t rfl h).left ≫ pullback.fst Z.hom t) hpq).trans
      ((congrArg (fun m : (Over.pullback t).obj X ⟶ (Over.pullback t).obj Z =>
        q ≫ m.left ≫ pullback.fst Z.hom t) hc).trans hq))

theorem morphism_compatible_of_base_overlap
    (h : (Over.pullback u).obj X ⟶ (Over.pullback u).obj Z)
    (hc : AbelianModuli.ReferenceFamily.Pullback.HomOverlap.CompositePullbackPoints.homAlongAt X u (pullback.fst u u) (pullback.fst u u ≫ u) rfl h =
      AbelianModuli.ReferenceFamily.Pullback.HomOverlap.CompositePullbackPoints.homAlongAt X u (pullback.snd u u) (pullback.fst u u ≫ u) pullback.condition.symm h) :
    AbelianModuli.ReferenceFamily.EtaleDescentLocal.EtaleDescent.Compatible u h :=
  pointwise_eq_of_base_overlap X u h hc _ _ pullback.condition

end AlgebraicGeometry.PELModuli.IntegralModel.MorphismBaseOverlap

end

end OAI
