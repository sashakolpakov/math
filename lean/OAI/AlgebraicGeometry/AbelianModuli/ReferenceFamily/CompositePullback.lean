import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Composite Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CompositePullback.CompositePullbackPoints

noncomputable section

/-! Actual points in an iterated base change, transported to the
composite base change, with both geometric projection equations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S Y W : Scheme.{0}} (X : Over S) (u : Y ⟶ S) (a : W ⟶ Y)

def comparison : pullback X.hom (a ≫ u) ≅ pullback (pullback.snd X.hom u) a :=
  (Over.forget W).mapIso ((Over.pullbackComp a u).app X)

theorem comparison_inv_fst :
    (comparison X u a).inv ≫ pullback.fst X.hom (a ≫ u) =
      pullback.fst (pullback.snd X.hom u) a ≫ pullback.fst X.hom u :=
  ((comparison X u a).inv_comp_eq).mpr (HilbertConstruction.Pullback.Comparisons.pullbackComp_hom_fst_fst X u a).symm

def point (x : W ⟶ pullback X.hom u) (hx : x ≫ pullback.snd X.hom u = a) :
    W ⟶ pullback X.hom (a ≫ u) :=
  pullback.lift x (𝟙 W) (hx.trans (Category.id_comp a).symm) ≫ (comparison X u a).inv

theorem point_fst (x : W ⟶ pullback X.hom u) (hx : x ≫ pullback.snd X.hom u = a) :
    point X u a x hx ≫ pullback.fst X.hom (a ≫ u) = x ≫ pullback.fst X.hom u := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => pullback.lift x (𝟙 W) (hx.trans (Category.id_comp a).symm) ≫ z)
      (comparison_inv_fst X u a)).trans (pullback.lift_fst_assoc _ _ _ _))

theorem point_snd (x : W ⟶ pullback X.hom u) (hx : x ≫ pullback.snd X.hom u = a) :
    point X u a x hx ≫ pullback.snd X.hom (a ≫ u) = 𝟙 W := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => pullback.lift x (𝟙 W) (hx.trans (Category.id_comp a).symm) ≫ z)
      (((Over.pullbackComp a u).inv.app X).w)).trans (pullback.lift_snd _ _ _))

def homAlong {Z : Over S} (h : (Over.pullback u).obj X ⟶ (Over.pullback u).obj Z) :
    (Over.pullback (a ≫ u)).obj X ⟶ (Over.pullback (a ≫ u)).obj Z :=
  (Over.pullbackComp a u).hom.app X ≫ (Over.pullback a).map h ≫ (Over.pullbackComp a u).inv.app Z

theorem point_homAlong {Z : Over S} (h : (Over.pullback u).obj X ⟶ (Over.pullback u).obj Z)
    (x : W ⟶ pullback X.hom u) (hx : x ≫ pullback.snd X.hom u = a) :
    point X u a x hx ≫ (homAlong X u a h).left ≫ pullback.fst Z.hom (a ≫ u) =
      x ≫ h.left ≫ pullback.fst Z.hom u := by
  let l := pullback.lift x (𝟙 W) (hx.trans (Category.id_comp a).symm)
  let m := ((Over.pullback a).map h).left
  have hm : m ≫ pullback.fst (pullback.snd Z.hom u) a =
      pullback.fst (pullback.snd X.hom u) a ≫ h.left := HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst h a
  change (l ≫ (comparison X u a).inv) ≫
    ((comparison X u a).hom ≫ m ≫ (comparison Z u a).inv) ≫ _ = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [comparison_inv_fst]
  rw [← Category.assoc m, hm]
  simp only [l, Category.assoc, pullback.lift_fst_assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CompositePullback.CompositePullbackPoints
