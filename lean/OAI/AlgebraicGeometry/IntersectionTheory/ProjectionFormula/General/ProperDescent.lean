import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ProperLeftDescent
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MovedComparison

/-! # Proper Descent -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ProperDescent

noncomputable section

/-! Native proper intersections descend in both original inputs in
all codimensions. The geometric intersection relation consequently
has only one rational-equivalence class of outputs. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

theorem intersection_congr (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a a' : X.RationalDimensionCycle p) (b b' : X.RationalDimensionCycle q)
    (ha : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p a a') (hb : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X q b b')
    (hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a b) (hp' : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a' b') :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (p + q) (Supports.ProperCycle.intersectionBilinear X m p q a b) (Supports.ProperCycle.intersectionBilinear X m p q a' b') := by
  obtain ⟨u, hu, _, hub, hub', he⟩ := MovedComparison.exists_moved X m p q a b b' hb
    (fun i : Fin 0 => Fin.elim0 i)
  have hleft := ProperLeftDescent.equivalent X m p q a u b hu hp hub
  have hua' := CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X p (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_symm X p hu) ha
  have hright := ProperLeftDescent.equivalent X m p q u a' b' hua' hub' hp'
  exact CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X (p + q) hleft (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X (p + q) he hright)

theorem proper_cycles (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a a' : X.RationalDimensionCycle p) (b b' : X.RationalDimensionCycle q)
    (ha : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p a a') (hb : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X q b b')
    (c c' : X.RationalDimensionCycle (p + q))
    (hc : CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X p q a b c) (hc' : CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X p q a' b' c') :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (p + q) c c' := by
  have he := CycleClass.Thom.IntersectionGeometry.isProperIntersectionCycle_unique X p q hc (Supports.ProperCycle.intersectionBilinear_isProper X m p q a b hc.1)
  have he' := CycleClass.Thom.IntersectionGeometry.isProperIntersectionCycle_unique X p q hc' (Supports.ProperCycle.intersectionBilinear_isProper X m p q a' b' hc'.1)
  rw [he, he']
  exact intersection_congr X m p q a a' b b' ha hb hc.1 hc'.1

theorem represents_unique (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (c c' : X.RationalDimensionCycle (p + q))
    (hc : CycleClass.Thom.IntersectionGeometry.RepresentsIntersection X p q a b c) (hc' : CycleClass.Thom.IntersectionGeometry.RepresentsIntersection X p q a b c') :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (p + q) c c' := by
  obtain ⟨a₁, b₁, c₁, ha₁, hb₁, h₁, hc₁⟩ := hc
  obtain ⟨a₂, b₂, c₂, ha₂, hb₂, h₂, hc₂⟩ := hc'
  have ha := CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X p (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_symm X p ha₁) ha₂
  have hb := CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X q (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_symm X q hb₁) hb₂
  have he := proper_cycles X m p q a₁ a₂ b₁ b₂ ha hb c₁ c₂ h₁ h₂
  exact CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X (p + q) hc₁
    (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X (p + q) he (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_symm X (p + q) hc₂))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ProperDescent
