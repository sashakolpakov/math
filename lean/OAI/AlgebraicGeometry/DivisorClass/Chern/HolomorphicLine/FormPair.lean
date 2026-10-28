import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CovectorPair
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.AntiForms
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.HermitianPair

/-! # Form Pair -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.FormPair

noncomputable section

/-! Frame-independent positive metric pairing of actual line-bundle-valued smooth forms. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff ComplexConjugate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

local instance lineFormPair_realDimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : FiniteDimensional ℝ V.analyticModel :=
  FiniteDimensional.trans ℝ ℂ V.analyticModel

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
  {U : Opens V.analyticSpace} (n : ℕ)

def holomorphicLineSmoothFormPair (a b : AntiForms.HolomorphicLineSmoothForm u U n) (x : U) : ℂ :=
  let hx := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain x.val
  (MetricWeight.holomorphicLineMetricWeight u x.val ⟨x.val, hx⟩ : ℂ) *
    Projective.CovectorPair.projectiveTangentCovectorPair V n x.val
      (a.val x.val ⟨x.val, x.property, hx⟩) (b.val x.val ⟨x.val, x.property, hx⟩)

theorem holomorphicLineSmoothFormPair_inFrame (a b : AntiForms.HolomorphicLineSmoothForm u U n)
    (i : V.analyticSpace) (x : U) (hi : x.val ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) :
    holomorphicLineSmoothFormPair V u n a b x =
      (MetricWeight.holomorphicLineMetricWeight u i ⟨x.val, hi⟩ : ℂ) *
        Projective.CovectorPair.projectiveTangentCovectorPair V n x.val
          (a.val i ⟨x.val, x.property, hi⟩) (b.val i ⟨x.val, x.property, hi⟩) := by
  let hx := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain x.val
  change (MetricWeight.holomorphicLineMetricWeight u x.val ⟨x.val, hx⟩ : ℂ) *
    Projective.CovectorPair.projectiveTangentCovectorPair V n x.val
      (a.val x.val ⟨x.val, x.property, hx⟩) (b.val x.val ⟨x.val, x.property, hx⟩) = _
  rw [a.property i x.val x.val x.property hi hx, b.property i x.val x.val x.property hi hx,
    Projective.CovectorPair.projectiveTangentCovectorPair_smul_left, Projective.CovectorPair.projectiveTangentCovectorPair_smul_right,
    MetricWeight.holomorphicLineMetricWeight_transition u i x.val x.val hi hx, Complex.ofReal_mul,
    Complex.normSq_eq_conj_mul_self]
  ring

theorem holomorphicLineSmoothFormPair_conj (a b : AntiForms.HolomorphicLineSmoothForm u U n) (x : U) :
    conj (holomorphicLineSmoothFormPair V u n b a x) = holomorphicLineSmoothFormPair V u n a b x := by
  dsimp only [holomorphicLineSmoothFormPair]
  rw [map_mul, Complex.conj_ofReal, Projective.CovectorPair.projectiveTangentCovectorPair_symm]

theorem holomorphicLineSmoothFormPair_add_left (a b c : AntiForms.HolomorphicLineSmoothForm u U n) (x : U) :
    holomorphicLineSmoothFormPair V u n (a + b) c x =
      holomorphicLineSmoothFormPair V u n a c x + holomorphicLineSmoothFormPair V u n b c x := by
  let hx := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain x.val
  let w : ℂ := MetricWeight.holomorphicLineMetricWeight u x.val ⟨x.val, hx⟩
  let A := a.val x.val ⟨x.val, x.property, hx⟩
  let B := b.val x.val ⟨x.val, x.property, hx⟩
  let C := c.val x.val ⟨x.val, x.property, hx⟩
  change w * Projective.CovectorPair.projectiveTangentCovectorPair V n x.val (A + B) C =
    w * Projective.CovectorPair.projectiveTangentCovectorPair V n x.val A C + w * Projective.CovectorPair.projectiveTangentCovectorPair V n x.val B C
  rw [Projective.CovectorPair.projectiveTangentCovectorPair_add_left, mul_add]

theorem holomorphicLineSmoothFormPair_smul_left (a b : AntiForms.HolomorphicLineSmoothForm u U n) (z : ℂ) (x : U) :
    holomorphicLineSmoothFormPair V u n (z • a) b x = conj z * holomorphicLineSmoothFormPair V u n a b x := by
  let hx := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain x.val
  let w : ℂ := MetricWeight.holomorphicLineMetricWeight u x.val ⟨x.val, hx⟩
  let A := a.val x.val ⟨x.val, x.property, hx⟩
  let B := b.val x.val ⟨x.val, x.property, hx⟩
  change w * Projective.CovectorPair.projectiveTangentCovectorPair V n x.val (z • A) B =
    conj z * (w * Projective.CovectorPair.projectiveTangentCovectorPair V n x.val A B)
  rw [Projective.CovectorPair.projectiveTangentCovectorPair_smul_left]
  ring

theorem holomorphicLineSmoothFormPair_self_re (a : AntiForms.HolomorphicLineSmoothForm u U n)
    (i : V.analyticSpace) (x : U) (hi : x.val ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) :
    (holomorphicLineSmoothFormPair V u n a a x).re =
      MetricWeight.holomorphicLineMetricWeight u i ⟨x.val, hi⟩ *
        (Projective.CovectorPair.projectiveTangentCovectorPair V n x.val
          (a.val i ⟨x.val, x.property, hi⟩) (a.val i ⟨x.val, x.property, hi⟩)).re := by
  rw [holomorphicLineSmoothFormPair_inFrame V u n a a i x hi, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem holomorphicLineSmoothFormPair_nonneg (a : AntiForms.HolomorphicLineSmoothForm u U n) (x : U) :
    0 ≤ (holomorphicLineSmoothFormPair V u n a a x).re := by
  let hx := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain x.val
  rw [holomorphicLineSmoothFormPair_self_re V u n a x.val x hx]
  exact mul_nonneg (MetricWeight.holomorphicLineMetricWeight_pos u x.val ⟨x.val, hx⟩).le
    (Projective.CovectorPair.projectiveTangentCovectorPair_nonneg V n x.val _)

theorem holomorphicLineSmoothFormPair_definite (a : AntiForms.HolomorphicLineSmoothForm u U n)
    (ha : ∀ x : U, (holomorphicLineSmoothFormPair V u n a a x).re = 0) : a = 0 := by
  apply AntiForms.holomorphicLineSmoothForm_ext
  intro i x
  have h := ha ⟨x.val, x.property.1⟩
  rw [holomorphicLineSmoothFormPair_self_re V u n a i ⟨x.val, x.property.1⟩ x.property.2] at h
  have hre : (Projective.CovectorPair.projectiveTangentCovectorPair V n x.val (a.val i x) (a.val i x)).re = 0 :=
    (mul_eq_zero.mp h).resolve_left (MetricWeight.holomorphicLineMetricWeight_pos u i ⟨x.val, x.property.2⟩).ne'
  apply Projective.CovectorPair.projectiveTangentCovectorPair_definite V n x.val (a.val i x)
  apply Complex.ext
  · exact hre
  · exact Projective.CovectorPair.projectiveTangentCovectorPair_self_im_zero V n x.val (a.val i x)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.FormPair
