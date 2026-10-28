import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.Integral
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrincipalCycle

/-! # Divisor Left Descent -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.DivisorLeftDescent

noncomputable section

/-! On an integral smooth projective scheme of every dimension, divisor
intersection respects rational equivalence of the divisor in every codimension. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.Integral.Cycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

theorem relation_single (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (d : X.RationalDimensionCycle 1) (hd : d ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1)
    (A : X.DimensionCycleSupport q)
    (hdA : ∀ B : X.DimensionCycleSupport 1, A.val ≤ B.val → d B = 0) :
    Supports.ProperCycle.intersectionBilinear X m 1 q d (Finsupp.single A 1) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (1 + q) := by
  obtain ⟨n, hn, f, hf, he⟩ := Principal.Integral.Denominator.exists_multiple X m d hd
  have ho (B : X.DimensionCycleSupport 1) (hAB : A.val ≤ B.val) :
      X.carrier.ord f (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) = 0 := by
    have h := congrArg (fun c : X.RationalDimensionCycle 1 => c B) he
    rw [Finsupp.smul_apply, hdA B hAB, smul_zero, Principal.Integral.Cycle.cycle_apply] at h
    exact_mod_cast h.symm
  obtain ⟨g, hg, hp⟩ := PrincipalCycle.exists_principal_intersection X m q A f hf ho
    (Principal.Integral.Cycle.cycle X f) (Principal.Integral.Cycle.cycle_apply X f)
  have hc := Supports.ProperCycle.intersectionBilinear_isProper X m 1 q (Principal.Integral.Cycle.cycle X f) (Finsupp.single A 1) hp.1
  have hzero := PrincipalCycle.intersection_rationally_zero X m q A f hf ho
    (Principal.Integral.Cycle.cycle X f) (Principal.Integral.Cycle.cycle_apply X f) _ hc
  change Supports.ProperCycle.intersectionBilinear X m 1 q (Principal.Integral.Cycle.cycle X f) (Finsupp.single A 1) - 0 ∈
    CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (1 + q) at hzero
  rw [sub_zero, ← he, map_smul, LinearMap.smul_apply] at hzero
  exact (Submodule.smul_mem_iff (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (1 + q)) (Nat.cast_ne_zero.mpr hn)).mp hzero

theorem relation_cycle (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (d : X.RationalDimensionCycle 1) (b : X.RationalDimensionCycle q) (hd : d ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1)
    (havoid : ∀ A ∈ b.support, ∀ B : X.DimensionCycleSupport 1, A.val ≤ B.val → d B = 0) :
    Supports.ProperCycle.intersectionBilinear X m 1 q d b ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (1 + q) := by
  have he : b = ∑ A ∈ b.support, (b A) • Finsupp.single A (1 : ℚ) := by
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    exact (Finsupp.sum_single b).symm
  rw [he, map_sum]
  apply Submodule.sum_mem
  intro A hA
  rw [map_smul]
  exact Submodule.smul_mem _ _ (relation_single X m q d hd A (havoid A hA))

theorem coefficient_zero_of_proper (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (q : ℕ)
    (a : X.RationalDimensionCycle 1) (b : X.RationalDimensionCycle q)
    (h : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 q a b) (A : X.DimensionCycleSupport q) (hA : A ∈ b.support)
    (B : X.DimensionCycleSupport 1) (hAB : A.val ≤ B.val) : a B = 0 := by
  by_contra ha
  have ht := h B (Finsupp.mem_support_iff.mpr ha) A hA A.val (fun _ hx => ⟨hAB hx, hx⟩)
  rw [A.property] at ht
  omega

theorem intersection_congr_left (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (a a' : X.RationalDimensionCycle 1) (b : X.RationalDimensionCycle q) (ha : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 a a')
    (hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 q a b) (hp' : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 q a' b) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (1 + q) (Supports.ProperCycle.intersectionBilinear X m 1 q a b)
      (Supports.ProperCycle.intersectionBilinear X m 1 q a' b) := by
  have hav (A : X.DimensionCycleSupport q) (hA : A ∈ b.support)
      (B : X.DimensionCycleSupport 1) (hAB : A.val ≤ B.val) : (a - a') B = 0 := by
    rw [Finsupp.sub_apply, coefficient_zero_of_proper X q a b hp A hA B hAB,
      coefficient_zero_of_proper X q a' b hp' A hA B hAB, sub_self]
  have h := relation_cycle X m q (a - a') b ha hav
  rw [map_sub, LinearMap.sub_apply] at h
  exact h

theorem proper_intersections_congr_left (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (a a' : X.RationalDimensionCycle 1) (b : X.RationalDimensionCycle q) (ha : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 a a')
    (c c' : X.RationalDimensionCycle (1 + q))
    (hc : CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X 1 q a b c)
    (hc' : CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X 1 q a' b c') : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (1 + q) c c' := by
  have he := CycleClass.Thom.IntersectionGeometry.isProperIntersectionCycle_unique X 1 q hc
    (Supports.ProperCycle.intersectionBilinear_isProper X m 1 q a b hc.1)
  have he' := CycleClass.Thom.IntersectionGeometry.isProperIntersectionCycle_unique X 1 q hc'
    (Supports.ProperCycle.intersectionBilinear_isProper X m 1 q a' b hc'.1)
  rw [he, he']
  exact intersection_congr_left X m q a a' b ha hc.1 hc'.1

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.DivisorLeftDescent
