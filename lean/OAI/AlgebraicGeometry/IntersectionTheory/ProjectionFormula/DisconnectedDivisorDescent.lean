import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Bilinear
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.Descent

/-! # Disconnected Divisor Descent -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DisconnectedDivisorDescent

noncomputable section

/-! Divisor intersection descends through rational equivalence on every
smooth projective presentation, including disconnected presentations. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

theorem meetProperly_restrict (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (C : irreducibleComponents X.carrier) (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (h : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a b) :
    CycleClass.Thom.IntersectionGeometry.MeetProperly (X.componentVariety C).presentation p q (Component.CycleMaps.restrict X C p a) (Component.CycleMaps.restrict X C q b) := by
  intro A hA B hB
  apply (Component.Bilinear.PairCycle.pair_proper_image X C p q A B).mp
  have ha : Component.CycleMaps.restrict X C p a A ≠ 0 := Finsupp.mem_support_iff.mp hA
  have hb : Component.CycleMaps.restrict X C q b B ≠ 0 := Finsupp.mem_support_iff.mp hB
  rw [Component.CycleMaps.restrict_apply] at ha hb
  exact h (Component.Image.supportImage X C p A) (Finsupp.mem_support_iff.mpr ha)
    (Component.Image.supportImage X C q B) (Finsupp.mem_support_iff.mpr hb)

theorem intersection_congr (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (a a' b b' : X.RationalDimensionCycle 1)
    (ha : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 a a') (hb : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 b b')
    (hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 1 a b) (hp' : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 1 a' b') :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 2 (Supports.ProperCycle.intersectionBilinear X m 1 1 a b)
      (Supports.ProperCycle.intersectionBilinear X m 1 1 a' b') := by
  apply (Component.Principal.CycleDecomposition.rationallyEquivalent_iff X m 2 _ _).mpr
  intro C
  let := Component.Image.component_relativeDimension X m C
  rw [Component.Bilinear.restrict_bilinear X m C 1 1 a b,
    Component.Bilinear.restrict_bilinear X m C 1 1 a' b']
  exact Divisor.Descent.intersection_congr (X.componentVariety C).presentation m _ _ _ _
    ((Component.Principal.CycleDecomposition.rationallyEquivalent_iff X m 1 a a').mp ha C)
    ((Component.Principal.CycleDecomposition.rationallyEquivalent_iff X m 1 b b').mp hb C)
    (meetProperly_restrict X C 1 1 a b hp) (meetProperly_restrict X C 1 1 a' b' hp')

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DisconnectedDivisorDescent
