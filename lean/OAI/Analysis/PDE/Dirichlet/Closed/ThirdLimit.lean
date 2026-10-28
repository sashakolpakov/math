import OAI.Analysis.PDE.Dirichlet.ThirdJetCompactness
import OAI.Analysis.PDE.Dirichlet.ThirdDerivativeLimit
import OAI.Analysis.PDE.Dirichlet.LocalSolutionLimit
import OAI.Analysis.Normed.Function.Holder.Banach.Construct

open Set Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
local instance closedThirdFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance closedThirdFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance closedThirdSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance closedThirdSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance closedThirdThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance closedThirdThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- A uniform third-jet estimate survives in the actual pointwise limit
as a Hölder field on the closed domain, with the original exponent. Its
interior values are proved to be the third derivatives of that limit. -/
theorem exists_closed_third_derivative_of_uniform_bound
    {r : E → ℝ} (hr : ContDiff ℝ 3 r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (u : ℕ → E → ℝ) (hu : ∀ k, ContDiff ℝ 3 (u k))
    (v : E → ℝ)
    (hv : ∀ x, r x < 0 → Tendsto (fun k => u k x) atTop (𝓝 (v x)))
    {α C M₀ M₁ M₂ M₃ : ℝ} (hα : 0 < α)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃)
    (h₀ : ∀ k x, r x ≤ 0 → ‖u k x‖ ≤ M₀)
    (h₁ : ∀ k x, r x ≤ 0 → ‖fderiv ℝ (u k) x‖ ≤ M₁)
    (h₂ : ∀ k x, r x ≤ 0 → ‖fderiv ℝ (fderiv ℝ (u k)) x‖ ≤ M₂)
    (h₃ : ∀ k x, r x ≤ 0 → ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (u k))) x‖ ≤ M₃)
    (hholder : ∀ k x, r x ≤ 0 → ∀ y, r y ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (u k))) x -
        fderiv ℝ (fderiv ℝ (fderiv ℝ (u k))) y‖ ≤ C*dist x y^α) :
    ContDiffOn ℝ 3 v {x | r x < 0} ∧
      ∃ T : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
        ‖T‖ ≤ max M₃ C ∧ ∀ x (hx : r x < 0),
          OAI.Analysis.Normed.Function.Holder.HolderMap.value T ⟨x, hx.le⟩ = fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x := by
  obtain ⟨_, G, H, T, _, _, _, hT, φ, hφ, _, hGlim, hHlim, hTlim, hTn, hTh⟩ :=
    exists_third_jet_locally_uniform_limit_on_closed_domain hr hreg u hu hα
      hM₁ hM₂ hM₃ h₀ h₁ h₂ h₃ hholder
  have hΩ : IsOpen {x | r x < 0} := isOpen_lt hr.continuous continuous_const
  have hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0} := by
    intro x hx
    change r x < 0 at hx
    change r x ≤ 0
    exact hx.le
  have hGΩ : TendstoLocallyUniformlyOn (fun k => fderiv ℝ (u (φ k)))
      (zeroExtend G) atTop {x | r x < 0} :=
    (locally_uniform_limit_zeroExtend hGlim).mono hΩD
  have hHΩ : TendstoLocallyUniformlyOn (fun k => fderiv ℝ (fderiv ℝ (u (φ k))))
      (zeroExtend H) atTop {x | r x < 0} :=
    (locally_uniform_limit_zeroExtend hHlim).mono hΩD
  have hTΩ : TendstoLocallyUniformlyOn (fun k => fderiv ℝ (fderiv ℝ (fderiv ℝ (u (φ k)))))
      (zeroExtend T) atTop {x | r x < 0} :=
    (locally_uniform_limit_zeroExtend hTlim).mono hΩD
  have hvφ : ∀ x ∈ {x | r x < 0}, Tendsto (fun k => u (φ k) x) atTop (𝓝 (v x)) :=
    fun x hx => (hv x hx).comp hφ.tendsto_atTop
  have hd := third_fderiv_of_locally_uniform_limit hΩ (fun k => hu (φ k)) hvφ hGΩ hHΩ hTΩ
  refine ⟨contDiffOn_three_of_locally_uniform_derivatives hΩ (fun k => hu (φ k)) hvφ hGΩ hHΩ hTΩ, ?_⟩
  let Q := max M₃ C
  have hQ : 0 ≤ Q := hM₃.trans (le_max_left _ _)
  let T₀ : {x | r x ≤ 0} →ᵇ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
    BoundedContinuousFunction.ofNormedAddCommGroup T hT M₃ hTn
  have hh : ∀ x y, ‖T₀ x-T₀ y‖ ≤ Q*dist x y^α := by
    intro x y
    exact (hTh x y).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg dist_nonneg _))
  let W := OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα.le T₀ hh
  have hWn : ‖W‖ ≤ Q := by
    apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_ofBounded_le hα.le T₀ hQ hh).trans
    apply max_le _ le_rfl
    exact (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le hT hM₃ hTn).trans
      (le_max_left _ _)
  refine ⟨W, hWn, ?_⟩
  intro x hx
  change T ⟨x, hx.le⟩ = _
  exact (zeroExtend_apply T hx.le).symm.trans (hd x hx).symm

end OAI.Analysis.PDE.Dirichlet
