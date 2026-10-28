import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowAssociativity

/-! # Chow Inner Swap -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowInnerSwap

noncomputable section

/-! Exchange the two outer factors of a nested graded Chow product. -/

open _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.GeneralChowIntersection OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowAssociativity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DegreeCast

theorem swap (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q t : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (a : ProperCycleLinearity.ChowQ X p) (b : ProperCycleLinearity.ChowQ X q) (c : ProperCycleLinearity.ChowQ X t) :
    DegreeCast.chow X (show p + (q + t) = q + (p + t) by omega)
      (General.GeneralChowIntersection.chowMap X m p (q + t) a (General.GeneralChowIntersection.chowMap X m q t b c)) =
    General.GeneralChowIntersection.chowMap X m q (p + t) b (General.GeneralChowIntersection.chowMap X m p t a c) := by
  rw [← General.ChowAssociativity.assoc X m p q t a b c, General.ChowAssociativity.chow_trans]
  have he := General.ChowAssociativity.cast_left X m (Nat.add_comm p q) t (General.GeneralChowIntersection.chowMap X m p q a b) c
  rw [General.ChowAssociativity.comm X m p q a b] at he
  have h := congrArg (DegreeCast.chow X (Nat.add_assoc q p t)) he
  rw [General.ChowAssociativity.chow_trans, General.ChowAssociativity.assoc X m q p t b a c] at h
  exact h

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowInnerSwap
