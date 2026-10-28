import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeSquare
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Square Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SquareProjection.CM

noncomputable section

/-! The canonical source comparisons preserve the projection to the
original arithmetic scheme. This identifies points of prescribed lifts
without adding a point-matching condition. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeSquare.CM

variable {S T U : Scheme} (f : U ⟶ T) (h : T ⟶ S) (x : U ⟶ S)
  (w : f ≫ h = x) (X : Over S)

theorem factor_hom_projection :
    (BaseChangeSquare.CM.factorIso f h x w X).hom.left ≫ pullback.fst (pullback.snd X.hom h) f ≫
      pullback.fst X.hom h = pullback.fst X.hom x := by
  subst x
  change (𝟙 _ ≫ ((Over.pullbackComp f h).app X).hom.left) ≫
    pullback.fst (pullback.snd X.hom h) f ≫ pullback.fst X.hom h = _
  rw [Category.id_comp]
  exact AbelianModuli.HilbertConstruction.Pullback.Comparisons.pullbackComp_hom_fst_fst X h f

theorem pullbackComp_inv_projection :
    ((Over.pullbackComp f h).app X).inv.left ≫ pullback.fst X.hom (f ≫ h) =
      pullback.fst (pullback.snd X.hom h) f ≫ pullback.fst X.hom h := by
  let e := (Over.pullbackComp f h).app X
  let P := pullback.fst (pullback.snd X.hom h) f ≫ pullback.fst X.hom h
  have hh : e.hom.left ≫ P = pullback.fst X.hom (f ≫ h) :=
    AbelianModuli.HilbertConstruction.Pullback.Comparisons.pullbackComp_hom_fst_fst X h f
  have he : e.inv.left ≫ e.hom.left = 𝟙 _ := congrArg Over.Hom.left e.inv_hom_id
  exact (congrArg (e.inv.left ≫ ·) hh.symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ P) he).trans (Category.id_comp P)))

variable {V : Scheme} (d : V ⟶ T) (e : V ⟶ U) (b : T ⟶ S) (c : U ⟶ S)
  (hw : d ≫ b = e ≫ c)

theorem square_hom_projection :
    (BaseChangeSquare.CM.squareIso d e b c hw X).hom.left ≫ pullback.fst (pullback.snd X.hom c) e ≫
      pullback.fst X.hom c =
    pullback.fst (pullback.snd X.hom b) d ≫ pullback.fst X.hom b := by
  let u := ((Over.pullbackComp d b).app X).inv.left
  let v := (BaseChangeSquare.CM.factorIso e c (d ≫ b) hw.symm X).hom.left
  let P := pullback.fst (pullback.snd X.hom c) e ≫ pullback.fst X.hom c
  change (u ≫ v) ≫ P = _
  exact (Category.assoc u v P).trans
    ((congrArg (u ≫ ·) (factor_hom_projection e c (d ≫ b) hw.symm X)).trans
      (pullbackComp_inv_projection d b X))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SquareProjection.CM
