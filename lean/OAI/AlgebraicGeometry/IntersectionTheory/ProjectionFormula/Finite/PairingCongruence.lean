import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CompatibleRelations

/-! # Pairing Congruence -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.PairingCongruence

noncomputable section

/-! Preserving the intersection class with every supported generator
preserves the intersection with the original finite rational cycle. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

theorem equivalent (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a a' : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (h : ∀ B ∈ b.support, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (p + q)
      (Supports.ProperCycle.intersectionBilinear X m p q a (Finsupp.single B 1))
      (Supports.ProperCycle.intersectionBilinear X m p q a' (Finsupp.single B 1))) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (p + q) (Supports.ProperCycle.intersectionBilinear X m p q a b) (Supports.ProperCycle.intersectionBilinear X m p q a' b) := by
  have he : b = ∑ B ∈ b.support, b B • Finsupp.single B (1 : ℚ) := by
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    exact (Finsupp.sum_single b).symm
  have hz : Supports.ProperCycle.intersectionBilinear X m p q (a - a') b ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (p + q) := by
    rw [he, map_sum]
    apply Submodule.sum_mem
    intro B hB
    rw [map_smul]
    apply Submodule.smul_mem
    simpa only [CycleClass.Thom.IntersectionGeometry.RationallyEquivalent, map_sub, LinearMap.sub_apply] using h B hB
  simpa only [CycleClass.Thom.IntersectionGeometry.RationallyEquivalent, map_sub, LinearMap.sub_apply] using hz

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.PairingCongruence
