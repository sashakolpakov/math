import Mathlib

noncomputable section
open Set _root_.MeasureTheory Filter
open scoped Topology

namespace OAI.Analysis.ODE.SmoothFlow

/-- Fixed compact time interval used for a parameter-dependent integral equation. -/
abbrev TimeInterval := Icc (-1 : ℝ) 1

def timeClamp : C(ℝ, TimeInterval) :=
  ⟨projIcc (-1) 1 (by norm_num), continuous_projIcc⟩

@[simp] theorem timeClamp_of_mem {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    timeClamp t = ⟨t,ht⟩ := projIcc_of_mem (by norm_num) ht

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Constant extension beyond the endpoints, as an actual continuous function. -/
def extendPath (γ : C(TimeInterval,E)) : C(ℝ,E) := γ.comp timeClamp

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[simp] theorem extendPath_apply (γ : C(TimeInterval,E)) (t : TimeInterval) :
    extendPath γ (t : ℝ) = γ t := by
  simp [extendPath]

def primitive (γ : C(TimeInterval,E)) (t : ℝ) : E :=
  ∫ r in 0..t, extendPath γ r

theorem primitive_hasDerivAt (γ : C(TimeInterval,E)) (t : ℝ) :
    HasDerivAt (primitive γ) (extendPath γ t) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((extendPath γ).continuous.intervalIntegrable _ _)
    (extendPath γ).continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    (extendPath γ).continuous.continuousAt

theorem continuous_primitive (γ : C(TimeInterval,E)) : Continuous (primitive γ) :=
  continuous_iff_continuousAt.mpr fun t => (primitive_hasDerivAt γ t).continuousAt

def volterraPath (γ : C(TimeInterval,E)) : C(TimeInterval,E) :=
  ⟨fun t => primitive γ t,(continuous_primitive γ).comp continuous_subtype_val⟩

theorem norm_volterraPath_apply_le (γ : C(TimeInterval,E)) (t : TimeInterval) :
    ‖volterraPath γ t‖ ≤ ‖γ‖ * |(t : ℝ)| := by
  simpa only [volterraPath,ContinuousMap.coe_mk,primitive,sub_zero] using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := (t : ℝ)) (f := fun r => extendPath γ r)
      (fun r _ => γ.norm_coe_le_norm (timeClamp r)))

theorem norm_volterraPath_le (γ : C(TimeInterval,E)) : ‖volterraPath γ‖ ≤ ‖γ‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg γ)).mpr
  intro t
  exact (norm_volterraPath_apply_le γ t).trans (by
    calc
      ‖γ‖ * |(t : ℝ)| ≤ ‖γ‖ * 1 :=
        mul_le_mul_of_nonneg_left (abs_le.mpr t.property) (norm_nonneg γ)
      _ = ‖γ‖ := mul_one _)

def volterraLinear : C(TimeInterval,E) →ₗ[ℝ] C(TimeInterval,E) where
  toFun := volterraPath
  map_add' γ η := by
    ext t
    change (∫ r in 0..(t : ℝ), extendPath γ r + extendPath η r) =
      (∫ r in 0..(t : ℝ), extendPath γ r) + ∫ r in 0..(t : ℝ), extendPath η r
    exact intervalIntegral.integral_add
      ((extendPath γ).continuous.intervalIntegrable _ _)
      ((extendPath η).continuous.intervalIntegrable _ _)
  map_smul' c γ := by
    ext t
    change (∫ r in 0..(t : ℝ), c • extendPath γ r) =
      c • ∫ r in 0..(t : ℝ), extendPath γ r
    exact intervalIntegral.integral_smul c _

/-- The actual Volterra integral operator is bounded linear, with norm at most one. -/
def volterra : C(TimeInterval,E) →L[ℝ] C(TimeInterval,E) :=
  volterraLinear.mkContinuous 1 (by
    intro γ
    change ‖volterraPath γ‖ ≤ 1 * ‖γ‖
    simpa only [one_mul] using norm_volterraPath_le γ)

@[simp] theorem volterra_apply (γ : C(TimeInterval,E)) (t : TimeInterval) :
    volterra γ t = primitive γ t := rfl

theorem norm_volterra_le : ‖volterra (E := E)‖ ≤ 1 := by
  apply LinearMap.mkContinuous_norm_le
  norm_num

omit [CompleteSpace E] in
@[simp] theorem primitive_zero (γ : C(TimeInterval,E)) : primitive γ 0 = 0 := by
  simp [primitive]

@[simp] theorem volterra_zero (γ : C(TimeInterval,E)) :
    volterra γ ⟨0,by norm_num⟩ = 0 := primitive_zero γ

/-- Differentiating the integral equation recovers its actual integrand. -/
theorem volterra_hasDerivAt (γ : C(TimeInterval,E)) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (extendPath (volterra γ)) (γ ⟨t,ht.1.le,ht.2.le⟩) t := by
  have heq : extendPath (volterra γ) =ᶠ[𝓝 t] primitive γ := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨hs.1.le,hs.2.le⟩
    simp [extendPath,timeClamp_of_mem hs',volterra_apply]
  have hd := primitive_hasDerivAt γ t
  have hval : extendPath γ t = γ ⟨t,ht.1.le,ht.2.le⟩ := by
    exact extendPath_apply γ ⟨t,ht.1.le,ht.2.le⟩
  rw [hval] at hd
  exact hd.congr_of_eventuallyEq heq

end OAI.Analysis.ODE.SmoothFlow
