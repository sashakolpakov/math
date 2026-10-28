import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.Integral

/-! # Left Descent -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.LeftDescent

noncomputable section

/-! On an integral smooth presentation, properly meeting divisor
intersection respects rational equivalence in the first variable. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.Integral.Cycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

theorem relation_single (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (d : X.RationalDimensionCycle 1) (hd : d ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1)
    (A : X.DimensionCycleSupport 1) (hdA : d A = 0) :
    Supports.ProperCycle.intersectionBilinear X m 1 1 d (Finsupp.single A 1) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 2 := by
  obtain ⟨n, hn, f, hf, he⟩ := Principal.Integral.Denominator.exists_multiple X m d hd
  have ho : X.carrier.ord f (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = 0 := by
    have h := congrArg (fun c : X.RationalDimensionCycle 1 => c A) he
    rw [Finsupp.smul_apply, hdA, smul_zero, Principal.Integral.Cycle.cycle_apply] at h
    exact_mod_cast h.symm
  obtain ⟨g, hg, hp⟩ := Principal.Integral.Divisor.exists_principal_intersection X m A f hf ho
    (Principal.Integral.Cycle.cycle X f) (Principal.Integral.Cycle.cycle_apply X f)
  have hc := Supports.ProperCycle.intersectionBilinear_isProper X m 1 1 (Principal.Integral.Cycle.cycle X f) (Finsupp.single A 1) hp.1
  have hzero := Principal.Integral.Cycle.intersection_rationally_zero X m A f hf ho _ hc
  change Supports.ProperCycle.intersectionBilinear X m 1 1 (Principal.Integral.Cycle.cycle X f) (Finsupp.single A 1) - 0 ∈
    CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 2 at hzero
  rw [sub_zero, ← he, map_smul, LinearMap.smul_apply] at hzero
  exact (Submodule.smul_mem_iff (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 2) (Nat.cast_ne_zero.mpr hn)).mp hzero

theorem relation_cycle (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (d b : X.RationalDimensionCycle 1) (hd : d ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1)
    (havoid : ∀ A ∈ b.support, d A = 0) :
    Supports.ProperCycle.intersectionBilinear X m 1 1 d b ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 2 := by
  have he : b = ∑ A ∈ b.support, (b A) • Finsupp.single A (1 : ℚ) := by
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    exact (Finsupp.sum_single b).symm
  rw [he, map_sum]
  apply Submodule.sum_mem
  intro A hA
  rw [map_smul]
  exact Submodule.smul_mem _ _ (relation_single X m d hd A (havoid A hA))

theorem coefficient_zero_of_proper (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (a b : X.RationalDimensionCycle 1) (h : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 1 a b)
    (A : X.DimensionCycleSupport 1) (hA : A ∈ b.support) : a A = 0 := by
  by_contra ha
  have ht := h A (Finsupp.mem_support_iff.mpr ha) A hA A.val (fun _ hx => ⟨hx, hx⟩)
  rw [A.property] at ht
  omega

theorem intersection_congr_left (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (a a' b : X.RationalDimensionCycle 1) (ha : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 a a')
    (hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 1 a b) (hp' : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 1 a' b) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 2 (Supports.ProperCycle.intersectionBilinear X m 1 1 a b)
      (Supports.ProperCycle.intersectionBilinear X m 1 1 a' b) := by
  have hav (A : X.DimensionCycleSupport 1) (hA : A ∈ b.support) : (a - a') A = 0 := by
    rw [Finsupp.sub_apply, coefficient_zero_of_proper X a b hp A hA,
      coefficient_zero_of_proper X a' b hp' A hA, sub_self]
  have h := relation_cycle X m (a - a') b ha hav
  rw [map_sub, LinearMap.sub_apply] at h
  exact h

theorem proper_intersections_congr_left (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (a a' b : X.RationalDimensionCycle 1) (ha : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 a a')
    (c c' : X.RationalDimensionCycle 2)
    (hc : CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X 1 1 a b c)
    (hc' : CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X 1 1 a' b c') : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 2 c c' := by
  have he := CycleClass.Thom.IntersectionGeometry.isProperIntersectionCycle_unique X 1 1 hc
    (Supports.ProperCycle.intersectionBilinear_isProper X m 1 1 a b hc.1)
  have he' := CycleClass.Thom.IntersectionGeometry.isProperIntersectionCycle_unique X 1 1 hc'
    (Supports.ProperCycle.intersectionBilinear_isProper X m 1 1 a' b hc'.1)
  rw [he, he']
  exact intersection_congr_left X m a a' b ha hc.1 hc'.1

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.LeftDescent
