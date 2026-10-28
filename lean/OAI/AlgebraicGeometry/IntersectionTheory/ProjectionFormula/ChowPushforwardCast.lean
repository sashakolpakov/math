import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardMap
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DegreeCast

/-! # Chow Pushforward Cast -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardCast

noncomputable section

/-! The native graded Chow pushforward respects equality transports
of source and target codimensions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardMap OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DegreeCast

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
  (m n : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]

theorem target (p q r : ℕ) (h : q = r) (hd : p + n = q + m) (hd' : p + n = r + m)
    (a : ProperCycleLinearity.ChowQ X p) : DegreeCast.chow Y h (ChowPushforwardMap.map f m n p q hd a) = ChowPushforwardMap.map f m n p r hd' a := by
  subst r
  rfl

theorem source (p q r : ℕ) (h : p = q) (hd : p + n = r + m) (hd' : q + n = r + m)
    (a : ProperCycleLinearity.ChowQ X p) : ChowPushforwardMap.map f m n q r hd' (DegreeCast.chow X h a) = ChowPushforwardMap.map f m n p r hd a := by
  subst q
  rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardCast
