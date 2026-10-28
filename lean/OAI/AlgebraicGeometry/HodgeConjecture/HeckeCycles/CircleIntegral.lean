import Mathlib

/-! # Circle Integral -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CircleIntegral.CM

noncomputable section

/-! Circle integration as a bounded complex-linear operator on continuous
boundary functions. This lets Banach-space Cauchy kernels provide joint
regularity in several complex variables. -/

open scoped Classical ContDiff
open _root_.Complex Set _root_.Metric

abbrev Boundary (c : ℂ) (R : ℝ) := sphere c R

instance boundary_compactSpace (c : ℂ) (R : ℝ) : CompactSpace (Boundary c R) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere c R)

def extend {c : ℂ} {R : ℝ} (f : C(Boundary c R, ℂ)) (z : ℂ) : ℂ :=
  if h : z ∈ sphere c R then f ⟨z, h⟩ else 0

@[simp] theorem extend_boundary {c : ℂ} {R : ℝ}
    (f : C(Boundary c R, ℂ)) (z : Boundary c R) : extend f z = f z := by
  simp only [extend, dite_eq_left z.property]

theorem extend_continuousOn {c : ℂ} {R : ℝ} (f : C(Boundary c R, ℂ)) :
    ContinuousOn (extend f) (sphere c R) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  simpa only [Set.domRestrict_def, extend_boundary] using f.continuous

theorem extend_circleIntegrable {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (f : C(Boundary c R, ℂ)) : CircleIntegrable (extend f) c R :=
  ContinuousOn.circleIntegrable hR (extend_continuousOn f)

theorem extend_add {c : ℂ} {R : ℝ} (f g : C(Boundary c R, ℂ)) :
    extend (f + g) = fun z => extend f z + extend g z := by
  funext z
  by_cases hz : z ∈ sphere c R
  · simp only [extend, dite_eq_left hz, ContinuousMap.add_apply]
  · simp only [extend, dite_eq_right hz, add_zero]

theorem extend_smul {c : ℂ} {R : ℝ} (a : ℂ) (f : C(Boundary c R, ℂ)) :
    extend (a • f) = fun z => a • extend f z := by
  funext z
  by_cases hz : z ∈ sphere c R
  · simp only [extend, dite_eq_left hz, ContinuousMap.smul_apply]
  · simp only [extend, dite_eq_right hz, smul_zero]

def integralLinear (c : ℂ) (R : ℝ) (hR : 0 ≤ R) : C(Boundary c R, ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∮ z in C(c, R), extend f z
  map_add' f g := by
    rw [extend_add]
    exact circleIntegral.integral_add (extend_circleIntegrable hR f) (extend_circleIntegrable hR g)
  map_smul' a f := by
    rw [extend_smul]
    exact circleIntegral.integral_smul a (extend f) c R

def integral (c : ℂ) (R : ℝ) (hR : 0 ≤ R) : C(Boundary c R, ℂ) →L[ℂ] ℂ :=
  (integralLinear c R hR).mkContinuous (2 * Real.pi * R) (by
    intro f
    apply circleIntegral.norm_integral_le_of_norm_le_const hR
    intro z hz
    change ‖extend f (⟨z, hz⟩ : Boundary c R)‖ ≤ ‖f‖
    rw [extend_boundary]
    exact f.norm_coe_le_norm ⟨z, hz⟩)

@[simp] theorem integral_apply (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (f : C(Boundary c R, ℂ)) :
    integral c R hR f = ∮ z in C(c, R), extend f z := rfl

/-- Any scalar function agreeing with the boundary function has the same
circle integral; the values outside the circle play no role. -/
theorem integral_eq_of_boundary (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (f : C(Boundary c R, ℂ)) (g : ℂ → ℂ)
    (h : ∀ z : Boundary c R, f z = g z) :
    integral c R hR f = ∮ z in C(c, R), g z := by
  apply circleIntegral.integral_congr hR
  intro z hz
  exact (extend_boundary f ⟨z, hz⟩).trans (h ⟨z, hz⟩)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CircleIntegral.CM
