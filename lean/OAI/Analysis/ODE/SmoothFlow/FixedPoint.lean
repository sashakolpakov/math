import OAI.Analysis.ODE.SmoothFlow.Integral

noncomputable section
open Set

namespace OAI.Analysis.ODE.SmoothFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {γ η : C(TimeInterval,E)} {x : E} {τ : ℝ}

theorem fixedPoint_initial
    (hγ : γ = ContinuousMap.const TimeInterval x + τ • volterra η) :
    γ ⟨0,by norm_num⟩ = x := by
  rw [hγ]
  simp

theorem fixedPoint_extend
    (hγ : γ = ContinuousMap.const TimeInterval x + τ • volterra η) (t : ℝ) :
    extendPath γ t = x + τ • extendPath (volterra η) t := by
  rw [hγ]
  rfl

/-- A solution of the actual Volterra fixed-point equation solves the
scaled differential equation at every interior time. -/
theorem fixedPoint_hasDerivAt
    (hγ : γ = ContinuousMap.const TimeInterval x + τ • volterra η)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (extendPath γ) (τ • η ⟨t,ht.1.le,ht.2.le⟩) t := by
  have hd := (hasDerivAt_const t x).add ((volterra_hasDerivAt η ht).const_smul τ)
  have heq : (extendPath γ : ℝ → E) =
      fun s => x + τ • extendPath (volterra η) s := funext (fixedPoint_extend hγ)
  rw [heq]
  have heq' : ((fun _ : ℝ => x) + τ • (extendPath (volterra η) : ℝ → E)) =
      (fun s => x + τ • extendPath (volterra η) s) := by
    ext s
    rfl
  rw [heq',zero_add] at hd
  exact hd

/-- Rescaling time removes the parameter multiplying the Volterra
operator. Both signs of the nonzero time scale are allowed. -/
theorem fixedPoint_rescaled_hasDerivAt
    (hγ : γ = ContinuousMap.const TimeInterval x + τ • volterra η)
    (hτ : τ ≠ 0) {t : ℝ} (ht : t / τ ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun s => extendPath γ (s / τ))
      (η ⟨t/τ,ht.1.le,ht.2.le⟩) t := by
  have hd := (fixedPoint_hasDerivAt hγ ht).scomp t ((hasDerivAt_id t).div_const τ)
  simpa only [Function.comp_def,id_eq,smul_smul,one_div,inv_mul_cancel₀ hτ,one_smul] using hd

theorem fixedPoint_rescaled_initial
    (hγ : γ = ContinuousMap.const TimeInterval x + τ • volterra η) :
    extendPath γ (0 / τ) = x := by
  rw [zero_div]
  exact (extendPath_apply γ ⟨0,by norm_num⟩).trans (fixedPoint_initial hγ)

/-- The nonlinear fixed-point equation gives the genuine autonomous
ODE, not merely an integral-equation surrogate. -/
theorem nonlinear_fixedPoint_rescaled_hasDerivAt
    (F : C(E,E))
    (hγ : γ = ContinuousMap.const TimeInterval x + τ • volterra (F.comp γ))
    (hτ : τ ≠ 0) {t : ℝ} (ht : t / τ ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun s => extendPath γ (s / τ))
      (F (extendPath γ (t/τ))) t := by
  have he : extendPath γ (t/τ) = γ ⟨t/τ,ht.1.le,ht.2.le⟩ :=
    extendPath_apply γ ⟨t/τ,ht.1.le,ht.2.le⟩
  rw [he]
  exact fixedPoint_rescaled_hasDerivAt hγ hτ ht

end OAI.Analysis.ODE.SmoothFlow
