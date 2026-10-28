import OAI.Analysis.PDE.Elliptic.Boundary.Schauder.Trace
import OAI.Analysis.PDE.Elliptic.Boundary.Schauder.Chart

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance driftHolderSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance driftHolderSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

/-- The first-order term created by flattening a smooth boundary has a
uniform C^α bound linear in the original C^α coefficient norm. No
derivatives of the coefficient enter the bound. -/
theorem exists_inverseChartDrift_holder_constant
    (G P : E → E) (hG : ContDiff ℝ 3 G) (hP : ContDiff ℝ 2 P)
    {S : Set E} (hS : IsCompact S) (hSc : Convex ℝ S)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x-y‖ ≤ 1)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : E → E →L[ℝ] E) (N : ℝ), 0 ≤ N →
      (∀ x ∈ S, ‖A (G x)‖ ≤ N) →
      (∀ x ∈ S, ∀ y ∈ S, ‖A (G x)-A (G y)‖ ≤ N * ‖G x-G y‖^α) →
      (∀ x ∈ S, ‖inverseChartDrift A G P x‖ ≤ C*N) ∧
      (∀ x ∈ S, ∀ y ∈ S,
        ‖inverseChartDrift A G P x - inverseChartDrift A G P y‖ ≤ C*N*‖x-y‖^α) := by
  obtain ⟨C₀, hC₀, hcoefficient⟩ := exists_chart_coefficient_holder_constant G P
    (hG.of_le (by norm_num)) hP hS hSc hdiam hα hα1
  let J := fun x => fderiv ℝ P (G x)
  let H := fderiv ℝ (fderiv ℝ G)
  have hJ : ContDiff ℝ 1 J := (hP.fderiv_right (by norm_num)).comp (hG.of_le (by norm_num))
  have hH : ContDiff ℝ 1 H := (hG.fderiv_right (m := 2) (by norm_num)).fderiv_right (by norm_num)
  obtain ⟨M₀, hM₀⟩ := hS.exists_bound_of_continuousOn hJ.continuous.continuousOn
  obtain ⟨M₁, hM₁⟩ := hS.exists_bound_of_continuousOn
    (hJ.continuous_fderiv (by norm_num)).continuousOn
  obtain ⟨M₂, hM₂raw⟩ := hS.exists_bound_of_continuousOn hH.continuous.norm.continuousOn
  have hM₂ : ∀ x ∈ S, ‖H x‖ ≤ M₂ := by
    intro x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hM₂raw x hx
  obtain ⟨M₃, hM₃⟩ := hS.exists_bound_of_continuousOn
    (hH.continuous_fderiv (by norm_num)).continuousOn
  let L := max 1 (max M₀ (max M₁ (max M₂ M₃)))
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have h₀ : M₀ ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have h₁ : M₁ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h₂ : M₂ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))
  have h₃ : M₃ ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))
  have hJn : ∀ x ∈ S, ‖J x‖ ≤ L := fun x hx => (hM₀ x hx).trans h₀
  have hHn : ∀ x ∈ S, ‖H x‖ ≤ L := fun x hx => (hM₂ x hx).trans h₂
  have hJh : ∀ x ∈ S, ∀ y ∈ S, ‖J x-J y‖ ≤ L*‖x-y‖ := by
    intro x hx y hy
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hJ.differentiable one_ne_zero z) (fun z hz => (hM₁ z hz).trans h₁) hSc hy hx
  have hHh : ∀ x ∈ S, ∀ y ∈ S, ‖H x-H y‖ ≤ L*‖x-y‖ := by
    intro x hx y hy
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hH.differentiable one_ne_zero z) (fun z hz => (hM₃ z hz).trans h₃) hSc hy hx
  let C := 3 * Module.finrank ℝ E * L^2 * C₀ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hnorm : Module.finrank ℝ E * L^2 * C₀ ≤ C := by
    have hp : 0 ≤ (Module.finrank ℝ E : ℝ) * L^2 * C₀ := by positivity
    dsimp [C]; nlinarith
  have hhold : 3 * Module.finrank ℝ E * L^2 * C₀ ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro A N hN hAn hAh
  obtain ⟨hBn, hBh⟩ := hcoefficient A N hN hAn hAh
  let B := fun z => pullbackEllipticOperator (fderiv ℝ P (G z)) (A (G z))
  obtain ⟨hn, hh⟩ := secondTrace_holder_bound J H B hL.le (mul_nonneg hC₀.le hN)
    hα1 hdiam hJn hHn hJh hHh hBn hBh
  constructor
  · intro x hx
    change ‖J x (secondTrace (H x) (B x))‖ ≤ C*N
    exact (hn x hx).trans (by nlinarith [mul_le_mul_of_nonneg_right hnorm hN])
  · intro x hx y hy
    change ‖J x (secondTrace (H x) (B x)) - J y (secondTrace (H y) (B y))‖ ≤ C*N*‖x-y‖^α
    exact (hh x hx y hy).trans (by
      have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hhold hN)
        (Real.rpow_nonneg (norm_nonneg (x-y)) α)
      nlinarith)

end OAI.Analysis.PDE.Elliptic
