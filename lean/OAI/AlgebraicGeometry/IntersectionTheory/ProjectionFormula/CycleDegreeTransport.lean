import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DegreeCast
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle

/-! # Cycle Degree Transport -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CycleDegreeTransport

noncomputable section

/-! Degree transport commutes with the actual finite cycle constructions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DegreeCast

theorem pushforward {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
    {p q : ℕ} (h : p = q) (r : ℕ) (a : X.RationalDimensionCycle p) :
    ProperCycleLinearity.cyclePushforward f q r (DegreeCast.cycle X h a) = ProperCycleLinearity.cyclePushforward f p r a := by
  subst q
  rfl

theorem principal (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {p q : ℕ} (h : p = q)
    (W : TopologicalSpace.IrreducibleCloseds X.carrier) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    DegreeCast.cycle X h (Principal.ClosedSectionCycle.principalCycle X p W g) = Principal.ClosedSectionCycle.principalCycle X q W g := by
  subst q
  rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CycleDegreeTransport
