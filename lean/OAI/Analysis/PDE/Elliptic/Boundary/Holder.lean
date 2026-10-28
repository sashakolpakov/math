import OAI.Analysis.PDE.Elliptic.Boundary.HolderOscillation
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! A genuine quantitative boundary C¹,α expansion for classical elliptic
solutions on a flat half-ball.  The slope is the actual Fréchet derivative. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter InnerProductSpace
open scoped Topology

theorem boundary_normal_derivative_between
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) (hv : ‖v‖ = 1) (u : E → ℝ) (hu : DifferentiableAt ℝ u 0)
    {r m M : ℝ} (hr : 0 < r)
    (hb : ∀ x, ‖x‖ ≤ r → 0 ≤ inner ℝ v x →
      m * inner ℝ v x ≤ u x ∧ u x ≤ M * inner ℝ v x) :
    boundarySlopeInf v u r ≤ fderiv ℝ u 0 v ∧ fderiv ℝ u 0 v ≤ boundarySlopeSup v u r := by
  have hb0 := hb 0 (by simpa using hr.le) (by simp)
  simp only [inner_zero_right, mul_zero] at hb0
  have hu0 : u 0 = 0 := le_antisymm hb0.2 hb0.1
  have hd : HasDerivAt (fun t : ℝ => u (t • v)) (fderiv ℝ u 0 v) 0 := by
    have hf : HasFDerivAt u (fderiv ℝ u 0) (id (0 : ℝ) • v) := by simpa using hu.hasFDerivAt
    simpa using! hf.comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℝ)).smul_const v)
  have hlim : Tendsto (fun t : ℝ => u (t • v) / t) (𝓝[>] 0) (𝓝 (fderiv ℝ u 0 v)) := by
    simpa [hu0, smul_eq_mul, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0,
      u (t • v) / t ∈ Icc (boundarySlopeInf v u r) (boundarySlopeSup v u r) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds] with t ht htr
    have ht0 : 0 < t := ht
    have hn : ‖t • v‖ ≤ r := by simp [norm_smul, hv, abs_of_pos ht0]; exact htr.le
    have hh : inner ℝ v (t • v) = t := by simp [real_inner_smul_right, hv]
    have hpoint := boundarySlope_pointwise_bounds v u hb (t • v) hn (by rw [hh]; exact ht0.le)
    rw [hh] at hpoint
    exact ⟨(le_div_iff₀ ht0).mpr hpoint.1, (div_le_iff₀ ht0).mpr hpoint.2⟩
  exact isClosed_Icc.mem_of_tendsto hlim hev

theorem boundary_first_order_holder
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    ∃ α : ℝ, 0 < α ∧ α < 1 ∧
      ∀ m M K : ℝ, m ≤ M → 0 ≤ K →
      ∃ C : ℝ, 0 < C ∧
      ∀ (v : EuclideanSpace ℝ ι), ‖v‖ = 1 →
      ∀ (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
        (u : EuclideanSpace ℝ ι → ℝ), ContDiff ℝ 2 u →
      (∀ x ∈ closedHalfBall v, m * inner ℝ v x ≤ u x ∧ u x ≤ M * inner ℝ v x) →
      (∀ x ∈ closedHalfBall v, ∀ w, lam * ‖w‖ ^ 2 ≤ inner ℝ w (A x w)) →
      (∀ x ∈ closedHalfBall v, ∀ w, inner ℝ w (A x w) ≤ L * ‖w‖ ^ 2) →
      (∀ x ∈ openHalfBall v, |ellipticTrace A u x| ≤ 2 * K * lam * Fintype.card ι) →
      ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x, ‖x‖ ≤ r → 0 ≤ inner ℝ v x →
        |u x - (fderiv ℝ u 0 v) * inner ℝ v x| ≤ C * r ^ α * inner ℝ v x := by
  obtain ⟨α, hα, hα1, hholder⟩ := boundary_quotient_holder_oscillation (ι := ι) hlam hL
  refine ⟨α, hα, hα1, ?_⟩
  intro m M K hmM hK
  obtain ⟨C, hC, hCbound⟩ := hholder m M K hmM hK
  refine ⟨C, hC, ?_⟩
  intro v hv A u hu hbound hlo hhi hLu r hr hr1 x hx ht
  have hb : ∀ y, ‖y‖ ≤ r → 0 ≤ inner ℝ v y →
      m * inner ℝ v y ≤ u y ∧ u y ≤ M * inner ℝ v y :=
    fun y hy hty => hbound y ⟨hy.trans hr1, hty⟩
  have hpoint := boundarySlope_pointwise_bounds v u hb x hx ht
  have hderiv := boundary_normal_derivative_between v hv u
    (hu.differentiable (by norm_num) 0) hr hb
  have hlow := mul_le_mul_of_nonneg_right hderiv.1 ht
  have hhigh := mul_le_mul_of_nonneg_right hderiv.2 ht
  have herror : |u x - (fderiv ℝ u 0 v) * inner ℝ v x| ≤
      boundarySlopeOsc v u r * inner ℝ v x := by
    rw [abs_le]
    dsimp [boundarySlopeOsc]
    constructor <;> nlinarith [hpoint.1, hpoint.2]
  exact herror.trans (mul_le_mul_of_nonneg_right (hCbound v hv A u hu hbound hlo hhi hLu r hr hr1) ht)

end OAI.Analysis.PDE.Elliptic
