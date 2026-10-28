import OAI.Analysis.PDE.Dirichlet.LocalJetCompactness
import OAI.Analysis.PDE.Dirichlet.CompactLimit

open Set Metric Filter
open scoped Topology Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem locally_uniform_limit_zeroExtend {E Y : Type*} [TopologicalSpace E]
    [UniformSpace Y] [Zero Y] {Ω : Set E} {u : ℕ → E → Y} {v : Ω → Y}
    (h : TendstoLocallyUniformly (fun k (x : Ω) ↦ u k x) v atTop) :
    TendstoLocallyUniformlyOn u (zeroExtend v) atTop Ω := by
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  have heq : (zeroExtend v) ∘ ((↑) : Ω → E) = v := by
    funext x
    exact zeroExtend_apply v x.property
  rw [heq]
  exact h

/-- A common locally C²,α bound yields one actual solution limit on the
whole open domain. The exponent and Hölder constant may vary with the
compact set, but not with the sequence index. -/
theorem exists_solution_limit_on_open {n : ℕ}
    {Ω : Set (CoordinateSpace n 4)} (hΩ : IsOpen Ω)
    (u : ℕ → CoordinateSpace n 4 → ℝ) (hu : ∀ k, ContDiff ℝ 2 (u k))
    {M₀ M₁ M₂ : ℝ}
    (h₀ : ∀ k x, x ∈ Ω → ‖u k x‖ ≤ M₀)
    (h₁ : ∀ k x, x ∈ Ω → ‖fderiv ℝ (u k) x‖ ≤ M₁)
    (h₂ : ∀ k x, x ∈ Ω → ‖fderiv ℝ (fderiv ℝ (u k)) x‖ ≤ M₂)
    (hholder : ∀ K : Set (CoordinateSpace n 4), IsCompact K → K ⊆ Ω →
      ∃ α C : ℝ, 0 < α ∧ ∀ k x, x ∈ K → ∀ y, y ∈ K →
        ‖fderiv ℝ (fderiv ℝ (u k)) x - fderiv ℝ (fderiv ℝ (u k)) y‖ ≤ C * dist x y ^ α)
    {F : ℕ → CoordinateSpace n 4 → ℝ} {g : CoordinateSpace n 4 → ℝ}
    (hF : ∀ x ∈ Ω, Tendsto (fun k ↦ F k x) atTop (𝓝 (g x)))
    (hg : ∀ x ∈ Ω, 0 < g x)
    (heq : ∀ k x, x ∈ Ω → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u k) x) = F k x)
    (hpos : ∀ k x, x ∈ Ω → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u k) x)).PosDef) :
    ∃ v : CoordinateSpace n 4 → ℝ, ContDiffOn ℝ 2 v Ω ∧
      (∀ x ∈ Ω, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots v x) = g x ∧
        (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots v x)).PosDef) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoLocallyUniformlyOn (fun k ↦ u (φ k)) v atTop Ω ∧
        TendstoLocallyUniformlyOn (fun k ↦ fderiv ℝ (u (φ k))) (fderiv ℝ v) atTop Ω ∧
        TendstoLocallyUniformlyOn (fun k ↦ fderiv ℝ (fderiv ℝ (u (φ k))))
          (fderiv ℝ (fderiv ℝ v)) atTop Ω := by
  obtain ⟨v₀, G₀, H₀, _, _, _, φ, hφ, hv₀, hG₀, hH₀⟩ :=
    exists_jet_locally_uniform_limit_on_open hΩ u hu h₀ h₁ h₂ hholder
  let v := zeroExtend v₀
  let G := zeroExtend G₀
  let H := zeroExtend H₀
  have hv : TendstoLocallyUniformlyOn (fun k ↦ u (φ k)) v atTop Ω :=
    locally_uniform_limit_zeroExtend hv₀
  have hG : TendstoLocallyUniformlyOn (fun k ↦ fderiv ℝ (u (φ k))) G atTop Ω :=
    locally_uniform_limit_zeroExtend hG₀
  have hH : TendstoLocallyUniformlyOn (fun k ↦ fderiv ℝ (fderiv ℝ (u (φ k)))) H atTop Ω :=
    locally_uniform_limit_zeroExtend hH₀
  have hvpoint : ∀ x ∈ Ω, Tendsto (fun k ↦ u (φ k) x) atTop (𝓝 (v x)) :=
    fun x hx ↦ hv.tendsto_at hx
  have hder := second_fderiv_of_locally_uniform_limit hΩ (fun k ↦ hu (φ k)) hvpoint hG hH
  refine ⟨v, contDiffOn_two_of_locally_uniform_derivatives hΩ
    (fun k ↦ hu (φ k)) hvpoint hG hH, ?_, φ, hφ, hv, ?_, ?_⟩
  · exact local_moore_equation_limit hΩ (fun k ↦ hu (φ k)) hvpoint hG hH
      (fun x hx ↦ (hF x hx).comp hφ.tendsto_atTop) hg
      (fun k x hx ↦ heq (φ k) x hx) (fun k x hx ↦ hpos (φ k) x hx)
  · rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe] at hG ⊢
    have heq : (fderiv ℝ v) ∘ ((↑) : Ω → CoordinateSpace n 4) = G ∘ (↑) := by
      funext x
      exact (hder x x.property).1
    rwa [heq]
  · rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe] at hH ⊢
    have heq : (fderiv ℝ (fderiv ℝ v)) ∘ ((↑) : Ω → CoordinateSpace n 4) = H ∘ (↑) := by
      funext x
      exact (hder x x.property).2
    rwa [heq]

end OAI.Analysis.PDE.Dirichlet
