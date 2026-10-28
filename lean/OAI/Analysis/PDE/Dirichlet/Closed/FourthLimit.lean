import OAI.Analysis.PDE.Dirichlet.Fourth.JetCompactness
import OAI.Analysis.PDE.Dirichlet.Fourth.DerivativeLimit
import OAI.Analysis.PDE.Dirichlet.LocalSolutionLimit
import OAI.Analysis.Normed.Function.Holder.Banach.Construct

open Set Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
local instance closedFourthFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance closedFourthFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance closedFourthSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance closedFourthSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance closedFourthThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance closedFourthThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance closedFourthFourthGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance closedFourthFourthSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- Uniform fourth-jet bounds give interior C⁴ regularity of the actual
pointwise limit and retain its fourth derivative as a Hölder field on the
entire closed domain, with no loss of exponent. -/
theorem exists_closed_fourth_derivative_of_uniform_bound
    {r : E → ℝ} (hr : ContDiff ℝ 3 r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (u : ℕ → E → ℝ) (hu : ∀ k, ContDiff ℝ 4 (u k))
    (v : E → ℝ)
    (hv : ∀ x, r x < 0 → Tendsto (fun k => u k x) atTop (𝓝 (v x)))
    {α C M₀ M₁ M₂ M₃ M₄ : ℝ} (hα : 0 < α)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃) (hM₄ : 0 ≤ M₄)
    (h₀ : ∀ k x, r x ≤ 0 → ‖u k x‖ ≤ M₀)
    (h₁ : ∀ k x, r x ≤ 0 → ‖fderiv ℝ (u k) x‖ ≤ M₁)
    (h₂ : ∀ k x, r x ≤ 0 → ‖fderiv ℝ (fderiv ℝ (u k)) x‖ ≤ M₂)
    (h₃ : ∀ k x, r x ≤ 0 → ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (u k))) x‖ ≤ M₃)
    (h₄ : ∀ k x, r x ≤ 0 → ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (u k)))) x‖ ≤ M₄)
    (hholder : ∀ k x, r x ≤ 0 → ∀ y, r y ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (u k)))) x -
        fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (u k)))) y‖ ≤ C*dist x y^α) :
    ContDiffOn ℝ 4 v {x | r x < 0} ∧
      ∃ Q : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
        ‖Q‖ ≤ max M₄ C ∧ ∀ x (hx : r x < 0),
          OAI.Analysis.Normed.Function.Holder.HolderMap.value Q ⟨x, hx.le⟩ = fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ v))) x := by
  obtain ⟨_, G, H, T, Q, _, _, _, _, hQ, φ, hφ, _, hGlim, hHlim, hTlim, hQlim, hQn, hQh⟩ :=
    exists_fourth_jet_locally_uniform_limit_on_closed_domain hr hreg u hu hα
      hM₁ hM₂ hM₃ hM₄ h₀ h₁ h₂ h₃ h₄ hholder
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
  have hQΩ : TendstoLocallyUniformlyOn
      (fun k => fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (u (φ k))))))
      (zeroExtend Q) atTop {x | r x < 0} :=
    (locally_uniform_limit_zeroExtend hQlim).mono hΩD
  have hvφ : ∀ x ∈ {x | r x < 0}, Tendsto (fun k => u (φ k) x) atTop (𝓝 (v x)) :=
    fun x hx => (hv x hx).comp hφ.tendsto_atTop
  have hd := fourth_fderiv_of_locally_uniform_limit hΩ (fun k => hu (φ k)) hvφ hGΩ hHΩ hTΩ hQΩ
  refine ⟨contDiffOn_four_of_locally_uniform_derivatives hΩ (fun k => hu (φ k))
    hvφ hGΩ hHΩ hTΩ hQΩ, ?_⟩
  let M := max M₄ C
  have hM : 0 ≤ M := hM₄.trans (le_max_left _ _)
  let Q₀ : {x | r x ≤ 0} →ᵇ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
    BoundedContinuousFunction.ofNormedAddCommGroup Q hQ M₄ hQn
  have hh : ∀ x y, ‖Q₀ x-Q₀ y‖ ≤ M*dist x y^α := by
    intro x y
    exact (hQh x y).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg dist_nonneg _))
  let W := OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα.le Q₀ hh
  have hWn : ‖W‖ ≤ M := by
    apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_ofBounded_le hα.le Q₀ hM hh).trans
    apply max_le _ le_rfl
    exact (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le hQ hM₄ hQn).trans
      (le_max_left _ _)
  refine ⟨W, hWn, ?_⟩
  intro x hx
  change Q ⟨x, hx.le⟩ = _
  exact (zeroExtend_apply Q hx.le).symm.trans (hd x hx).symm

end OAI.Analysis.PDE.Dirichlet
