import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.Divisor

/-! # Chow Map -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.ChowMap

noncomputable section

/-! A uniform exact divisor Chow map, with native proper-cycle evaluation. -/

open _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
  [SmoothOfRelativeDimension m X.structureMap]

include m

def map : ProperCycleLinearity.ChowQ X 1 →ₗ[ℚ] ProperCycleLinearity.ChowQ X q →ₗ[ℚ] ProperCycleLinearity.ChowQ X (1 + q) :=
  (General.Divisor.chowIntersection_map_exists X m q).choose

theorem graph (a : ProperCycleLinearity.ChowQ X 1) (b : ProperCycleLinearity.ChowQ X q) :
    ProperCycleLinearity.chowIntersection X 1 q a b = {map X m q a b} :=
  (General.Divisor.chowIntersection_map_exists X m q).choose_spec a b

theorem of_proper (a : X.RationalDimensionCycle 1) (b : X.RationalDimensionCycle q)
    (c : X.RationalDimensionCycle (1 + q)) (hc : CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X 1 q a b c) :
    map X m q (ProperCycleLinearity.cycleToChowQ X 1 a) (ProperCycleLinearity.cycleToChowQ X q b) = ProperCycleLinearity.cycleToChowQ X (1 + q) c := by
  have h := (ProperCycleLinearity.chowIntersection_mk_iff X 1 q a b c).mpr
    (CycleClass.Thom.IntersectionGeometry.representsIntersection_of_proper X 1 q a b c hc)
  rw [graph X m q, Set.mem_singleton_iff] at h
  exact h.symm

theorem of_bilinear (a : X.RationalDimensionCycle 1) (b : X.RationalDimensionCycle q)
    (hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 q a b) :
    map X m q (ProperCycleLinearity.cycleToChowQ X 1 a) (ProperCycleLinearity.cycleToChowQ X q b) =
      ProperCycleLinearity.cycleToChowQ X (1 + q) (Supports.ProperCycle.intersectionBilinear X m 1 q a b) :=
  of_proper X m q a b _ (Supports.ProperCycle.intersectionBilinear_isProper X m 1 q a b hp)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.ChowMap
