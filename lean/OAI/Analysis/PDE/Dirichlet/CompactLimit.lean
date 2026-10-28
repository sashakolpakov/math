import OAI.Analysis.PDE.Dirichlet.JetCompactness
import OAI.Analysis.PDE.Dirichlet.EquationLimit

open Set Metric Filter
open scoped Topology Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

def zeroExtend {E Y : Type*} [Zero Y] {K : Set E} (f : K → Y) (x : E) : Y := by
  classical
  exact if hx : x ∈ K then f ⟨x, hx⟩ else 0

theorem zeroExtend_apply {E Y : Type*} [Zero Y] {K : Set E}
    (f : K → Y) {x : E} (hx : x ∈ K) : zeroExtend f x = f ⟨x, hx⟩ := by
  simp only [zeroExtend, dite_eq_left hx]

theorem uniform_limit_zeroExtend {E Y : Type*} [UniformSpace Y] [Zero Y]
    {K : Set E} {u : ℕ → E → Y} {v : K → Y}
    (h : TendstoUniformly (fun k (x : K) ↦ u k x) v atTop) :
    TendstoUniformlyOn u (zeroExtend v) atTop K := by
  intro U hU
  filter_upwards [h U hU] with k hk
  intro x hx
  simpa only [zeroExtend_apply v hx] using hk ⟨x, hx⟩

/-- A bounded sequence of genuine solutions with a common Hessian Hölder
bound has an actual C² solution limit on the interior of a compact convex
set. One subsequence converges at all three derivative levels. -/
theorem exists_local_solution_limit_on_compact {n : ℕ}
    {K : Set (CoordinateSpace n 4)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (u : ℕ → CoordinateSpace n 4 → ℝ) (hu : ∀ k, ContDiff ℝ 2 (u k))
    {α C M₀ M₁ M₂ : ℝ} (hα : 0 < α)
    (h₀ : ∀ k x, x ∈ K → ‖u k x‖ ≤ M₀)
    (h₁ : ∀ k x, x ∈ K → ‖fderiv ℝ (u k) x‖ ≤ M₁)
    (h₂ : ∀ k x, x ∈ K → ‖fderiv ℝ (fderiv ℝ (u k)) x‖ ≤ M₂)
    (hholder : ∀ k x, x ∈ K → ∀ y, y ∈ K →
      ‖fderiv ℝ (fderiv ℝ (u k)) x - fderiv ℝ (fderiv ℝ (u k)) y‖ ≤ C * (dist x y) ^ α)
    {F : ℕ → CoordinateSpace n 4 → ℝ} {g : CoordinateSpace n 4 → ℝ}
    (hF : ∀ x ∈ interior K, Tendsto (fun k ↦ F k x) atTop (𝓝 (g x)))
    (hg : ∀ x ∈ interior K, 0 < g x)
    (heq : ∀ k x, x ∈ interior K → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u k) x) = F k x)
    (hpos : ∀ k x, x ∈ interior K → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u k) x)).PosDef) :
    ∃ v : CoordinateSpace n 4 → ℝ, ContDiffOn ℝ 2 v (interior K) ∧
      (∀ x ∈ interior K, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots v x) = g x ∧
        (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots v x)).PosDef) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoUniformlyOn (fun k ↦ u (φ k)) v atTop K ∧
        TendstoUniformlyOn (fun k ↦ fderiv ℝ (u (φ k))) (fderiv ℝ v) atTop (interior K) ∧
        TendstoUniformlyOn (fun k ↦ fderiv ℝ (fderiv ℝ (u (φ k))))
          (fderiv ℝ (fderiv ℝ v)) atTop (interior K) := by
  obtain ⟨v₀, G₀, H₀, _, _, _, φ, hφ, hv₀, hG₀, hH₀⟩ :=
    exists_jet_uniform_limit_on_compact_convex hK hconv u hu hα h₀ h₁ h₂ hholder
  let v := zeroExtend v₀
  let G := zeroExtend G₀
  let H := zeroExtend H₀
  have hv : TendstoUniformlyOn (fun k ↦ u (φ k)) v atTop K := uniform_limit_zeroExtend hv₀
  have hG : TendstoUniformlyOn (fun k ↦ fderiv ℝ (u (φ k))) G atTop (interior K) :=
    (uniform_limit_zeroExtend hG₀).mono interior_subset
  have hH : TendstoUniformlyOn (fun k ↦ fderiv ℝ (fderiv ℝ (u (φ k)))) H atTop (interior K) :=
    (uniform_limit_zeroExtend hH₀).mono interior_subset
  have hvpoint : ∀ x ∈ interior K, Tendsto (fun k ↦ u (φ k) x) atTop (𝓝 (v x)) :=
    fun x hx ↦ hv.tendsto_at (interior_subset hx)
  have hGlocal := hG.tendstoLocallyUniformlyOn
  have hHlocal := hH.tendstoLocallyUniformlyOn
  have hder := second_fderiv_of_locally_uniform_limit isOpen_interior
    (fun k ↦ hu (φ k)) hvpoint hGlocal hHlocal
  refine ⟨v, contDiffOn_two_of_locally_uniform_derivatives isOpen_interior
    (fun k ↦ hu (φ k)) hvpoint hGlocal hHlocal, ?_, φ, hφ, hv, ?_, ?_⟩
  · exact local_moore_equation_limit isOpen_interior (fun k ↦ hu (φ k)) hvpoint hGlocal hHlocal
      (fun x hx ↦ (hF x hx).comp hφ.tendsto_atTop) hg
      (fun k x hx ↦ heq (φ k) x hx) (fun k x hx ↦ hpos (φ k) x hx)
  · intro U hU
    filter_upwards [hG U hU] with k hk
    intro x hx
    simpa only [(hder x hx).1] using hk x hx
  · intro U hU
    filter_upwards [hH U hU] with k hk
    intro x hx
    simpa only [(hder x hx).2] using hk x hx

end OAI.Analysis.PDE.Dirichlet
