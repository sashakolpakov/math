import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.SquareProjection
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeEvaluation

/-! # Point Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PointProjection.CM

noncomputable section

/-! Original and local source points are related by the canonical
pullback comparison. Their projections to the arithmetic source agree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeSquare.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BaseChangeEvaluation.CM

variable {S T U V : Scheme} (d : V ⟶ T) (e : V ⟶ U) (b : T ⟶ S) (c : U ⟶ S)
  (w : d ≫ b = e ≫ c) (X : Over S) (A : Over V)

abbrev localSource := (Over.pullback d).obj ((Over.pullback b).obj X)
abbrev genericSource := (Over.pullback c).obj X

def originalPoint (z : A ⟶ localSource d b X) : (Over.map e).obj A ⟶ genericSource c X :=
  BaseChangeEvaluation.CM.pointsEquiv e A (genericSource c X) (z ≫ (BaseChangeSquare.CM.squareIso d e b c w X).hom)

def localPoint (z : (Over.map e).obj A ⟶ genericSource c X) : A ⟶ localSource d b X :=
  (BaseChangeEvaluation.CM.pointsEquiv e A (genericSource c X)).symm z ≫ (BaseChangeSquare.CM.squareIso d e b c w X).inv

theorem original_local (z : (Over.map e).obj A ⟶ genericSource c X) :
    originalPoint d e b c w X A (localPoint d e b c w X A z) = z := by
  simp only [originalPoint, localPoint, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, Equiv.apply_symm_apply]

theorem original_projection (z : A ⟶ localSource d b X) :
    (originalPoint d e b c w X A z).left ≫ pullback.fst X.hom c =
      z.left ≫ pullback.fst (pullback.snd X.hom b) d ≫ pullback.fst X.hom b := by
  change ((z.left ≫ (BaseChangeSquare.CM.squareIso d e b c w X).hom.left) ≫
    pullback.fst (pullback.snd X.hom c) e) ≫ pullback.fst X.hom c = _
  have h := congrArg (z.left ≫ ·)
    (SquareProjection.CM.square_hom_projection X d e b c w)
  simpa only [Category.assoc] using h

theorem local_projection (z : (Over.map e).obj A ⟶ genericSource c X) :
    (localPoint d e b c w X A z).left ≫ pullback.fst (pullback.snd X.hom b) d ≫
        pullback.fst X.hom b = z.left ≫ pullback.fst X.hom c := by
  have h := original_projection d e b c w X A (localPoint d e b c w X A z)
  rw [original_local] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PointProjection.CM
