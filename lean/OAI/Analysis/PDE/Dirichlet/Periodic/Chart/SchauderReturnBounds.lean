import OAI.Analysis.PDE.Dirichlet.Periodic.Chart.SchauderReturnAnalytic
import OAI.Analysis.PDE.Dirichlet.Periodic.Chart.LocalizationJets

open Set Metric
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance returnBoundsFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance returnBoundsFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance returnBoundsSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance returnBoundsSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The four bounds in the local Schauder estimate, imposed only on S. -/
structure SchauderJetBoundsOn (u : E → ℝ) (S : Set E) (α M : ℝ) : Prop where
  value : ∀ x ∈ S, |u x| ≤ M
  first : ∀ x ∈ S, ‖fderiv ℝ u x‖ ≤ M
  second : ∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ M
  second_holder : ∀ x ∈ S, ∀ y ∈ S,
    ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ M*‖x-y‖^α

omit [FiniteDimensional ℝ E] in
theorem SchauderJetBoundsOn.congr_germ
    {f g : E → ℝ} {S : Set E} {α M : ℝ} (hf : SchauderJetBoundsOn f S α M)
    (hfg : ∀ x ∈ S, f =ᶠ[𝓝 x] g) : SchauderJetBoundsOn g S α M := by
  constructor
  · intro x hx
    rw [← (hfg x hx).eq_of_nhds]
    exact hf.value x hx
  · intro x hx
    rw [← (hfg x hx).fderiv_eq (𝕜 := ℝ)]
    exact hf.first x hx
  · intro x hx
    rw [← ((hfg x hx).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]
    exact hf.second x hx
  · intro x hx y hy
    rw [← ((hfg x hx).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ),
      ← ((hfg y hy).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]
    exact hf.second_holder x hx y hy

/-- Pulling four local jet bounds through a fixed inverse chart costs a
single fixed constant. T need not be convex or have interior. -/
theorem exists_schauder_composition_bound
    (P : E → E) (hP : ContDiff ℝ 3 P) {D S T : Set E}
    (hDc : IsCompact D) (hDv : Convex ℝ D) (hSv : Convex ℝ S)
    (hTD : T ⊆ D) (hPS : MapsTo P T S)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : E → ℝ, ContDiff ℝ 2 w → ∀ M : ℝ, 0 ≤ M →
      SchauderJetBoundsOn w S α M →
      SchauderJetBoundsOn (fun z ↦ w (P z)) T α (C*M) := by
  have hDP : ContDiff ℝ 2 (fderiv ℝ P) := hP.fderiv_right (by norm_num)
  obtain ⟨L₁,hL₁⟩ := hDc.exists_bound_of_continuousOn hDP.continuous.continuousOn
  obtain ⟨L₂,hL₂⟩ := hDc.exists_bound_of_continuousOn
    (hP.continuous_iteratedFDeriv (by norm_num : (2 : ℕ∞ω) ≤ 3)).continuousOn
  obtain ⟨L₃,hL₃⟩ := hDc.exists_bound_of_continuousOn
    (hP.continuous_iteratedFDeriv (by norm_num : (3 : ℕ∞ω) ≤ 3)).continuousOn
  let L := max L₁ 0+max L₂ 0+max L₃ 0+1
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hP1 x (hx : x ∈ D) : ‖fderiv ℝ P x‖ ≤ L := (hL₁ x hx).trans (by
    dsimp [L]; linarith [le_max_left L₁ 0,le_max_right L₂ 0,le_max_right L₃ 0])
  have hP2 x (hx : x ∈ D) : ‖iteratedFDeriv ℝ 2 P x‖ ≤ L := (hL₂ x hx).trans (by
    dsimp [L]; linarith [le_max_right L₁ 0,le_max_left L₂ 0,le_max_right L₃ 0])
  have hP3 x (hx : x ∈ D) : ‖iteratedFDeriv ℝ 3 P x‖ ≤ L := (hL₃ x hx).trans (by
    dsimp [L]; linarith [le_max_right L₁ 0,le_max_right L₂ 0,le_max_left L₃ 0])
  obtain ⟨R,hR⟩ := hDc.exists_bound_of_continuousOn continuous_id.continuousOn
  let d := 1+2*max R 0
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hscale x (hx : x ∈ D) y (hy : y ∈ D) : ‖x-y‖ ≤ d*‖x-y‖^α := by
    apply le_bounded_rpow (norm_nonneg _) (by positivity) _ hα hα1
    exact (norm_sub_le x y).trans (by
      have hx' : ‖x‖ ≤ R := hR x hx
      have hy' : ‖y‖ ≤ R := hR y hy
      linarith [le_max_left R 0])
  let A := L^2+L
  let B := L^2*L^α+(3*L^2+L)*d
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let C := 1+L+A+B
  have hC : 0 < C := by dsimp [C]; positivity
  have hc0 : 1 ≤ C := by dsimp [C]; linarith
  have hc1 : L ≤ C := by dsimp [C]; linarith
  have hc2 : A ≤ C := by dsimp [C]; linarith
  have hcH : B ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro w hw M hM hb
  obtain ⟨hwn,hwh⟩ := chart_hessian_holder_between_sets hw hP hDv hSv hTD hPS
    hL hM hd hα hscale hb.first hb.second hb.second_holder hP1 hP2 hP3
  constructor
  · intro x hx
    apply (hb.value (P x) (hPS hx)).trans
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc0 hM
  · intro x hx
    exact (chart_first_derivative_bound hw hP hM (hb.first (P x) (hPS hx))
      (hP1 x (hTD hx))).trans (mul_le_mul_of_nonneg_right hc1 hM)
  · intro x hx
    exact (hwn x hx).trans (mul_le_mul_of_nonneg_right hc2 hM)
  · intro x hx y hy
    exact (hwh x hx y hy).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcH hM) (Real.rpow_nonneg (norm_nonneg _) _))

end OAI.Analysis.PDE.Dirichlet
