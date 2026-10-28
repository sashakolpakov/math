import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.SupportPrincipalIntersection
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.DivisorLeftDescent
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.UnitAvoidance

/-! # Principal Cycle Descent -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.PrincipalCycleDescent

noncomputable section

/-! Moving the divisor removes every auxiliary unit condition: any
proper intersection with a principal cycle relation is rationally zero. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

theorem principal (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (W : X.DimensionCycleSupport k) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hg : g ≠ 0)
    (a : X.RationalDimensionCycle 1) (hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 (k + 1) a (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g)) :
    Supports.ProperCycle.intersectionBilinear X m 1 (k + 1) a (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (1 + (k + 1)) := by
  let d := Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g
  obtain ⟨a', ha', _, hgood⟩ := Support.UnitAvoidance.move X m k W g hg ∅ a
  have hp' : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 (k + 1) a' d := by
    intro D hD A hA
    exact Support.Principal.proper X m k D W g (hgood D hD).2 D (by simp) A hA
  have hz : Supports.ProperCycle.intersectionBilinear X m 1 (k + 1) a' d ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (1 + (k + 1)) := by
    have he : a' = ∑ D ∈ a'.support, a' D • Finsupp.single D (1 : ℚ) := by
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
      exact (Finsupp.sum_single a').symm
    rw [he, map_sum, LinearMap.sum_apply]
    apply Submodule.sum_mem
    intro D hD
    rw [map_smul, LinearMap.smul_apply]
    exact Submodule.smul_mem _ _
      (Support.SupportPrincipalIntersection.intersection_rationally_zero X m k D W (hgood D hD).1 g hg
        (hgood D hD).2)
  have hrel := DivisorLeftDescent.intersection_congr_left X m (k + 1) a a' d ha' hp hp'
  simpa only [sub_add_cancel] using (Submodule.add_mem (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (1 + (k + 1))) hrel hz :
      Supports.ProperCycle.intersectionBilinear X m 1 (k + 1) a d - Supports.ProperCycle.intersectionBilinear X m 1 (k + 1) a' d +
        Supports.ProperCycle.intersectionBilinear X m 1 (k + 1) a' d ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (1 + (k + 1)))

theorem generator (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (d : X.RationalDimensionCycle (k + 1)) (hd : CycleClass.Thom.IntersectionGeometry.IsPrincipalDivisor X (k + 1) d)
    (a : X.RationalDimensionCycle 1) (hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 (k + 1) a d) :
    Supports.ProperCycle.intersectionBilinear X m 1 (k + 1) a d ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (1 + (k + 1)) := by
  obtain ⟨W, hW, g, hg, rfl⟩ := (Principal.ClosedSectionCycle.isPrincipalDivisor_iff X (k + 1) d).mp hd
  have hcod : X.supportCodimension W = k := by omega
  exact principal X m k ⟨W, hcod⟩ g hg a hp

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.PrincipalCycleDescent
