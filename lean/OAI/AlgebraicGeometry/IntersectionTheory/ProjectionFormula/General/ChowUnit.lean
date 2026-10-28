import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowAssociativity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowZero
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ZeroComponents

/-! # Chow Unit -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowUnit

noncomputable section

/-! The reduced fundamental cycle is the unit for the general Chow
intersection, including schemes with several connected components. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p : ℕ) [SmoothOfRelativeDimension m X.structureMap]

theorem cycle_left (a : X.RationalDimensionCycle p) :
    Supports.ProperCycle.intersectionBilinear X m 0 p (ProperCycleLinearity.fundamentalCycle X) a = DegreeCast.cycle X (Nat.zero_add p).symm a := by
  have hp := IntersectionZero.meetProperly_zero_left X m p (ProperCycleLinearity.fundamentalCycle X) a
  have he := CycleClass.Thom.IntersectionGeometry.isProperIntersectionCycle_unique X 0 p
    (Supports.ProperCycle.intersectionBilinear_isProper X m 0 p (ProperCycleLinearity.fundamentalCycle X) a hp)
    (ChowZero.cycleIntersection_isProper X m p (ProperCycleLinearity.fundamentalCycle X) a)
  rw [he]
  change DegreeCast.cycle X (Nat.zero_add p).symm
    (Component.Action.cycleAction X p (ProperCycleLinearity.fundamentalCycle X) a) = _
  congr 1
  ext C
  rw [ZeroComponents.cycleAction_apply_component X m, ZeroComponents.fundamentalCycle_apply X m,
    one_mul]

theorem left (a : ProperCycleLinearity.ChowQ X p) :
    GeneralChowIntersection.chowMap X m 0 p (ProperCycleLinearity.cycleToChowQ X 0 (ProperCycleLinearity.fundamentalCycle X)) a =
      DegreeCast.chow X (Nat.zero_add p).symm a := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X p a
  rw [ChowAssociativity.mk_proper X m 0 p _ _
    (IntersectionZero.meetProperly_zero_left X m p _ _), cycle_left,
    DegreeCast.chow_mk]

theorem right (a : ProperCycleLinearity.ChowQ X p) :
    GeneralChowIntersection.chowMap X m p 0 a (ProperCycleLinearity.cycleToChowQ X 0 (ProperCycleLinearity.fundamentalCycle X)) = a := by
  have he := ChowAssociativity.comm X m 0 p (ProperCycleLinearity.cycleToChowQ X 0 (ProperCycleLinearity.fundamentalCycle X)) a
  rw [left, ChowAssociativity.chow_trans] at he
  exact he.symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowUnit
