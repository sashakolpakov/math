import OAI.Analysis.PDE.Dirichlet.Periodic.Chart.LocalizationAlgebra
import OAI.Analysis.PDE.Dirichlet.Periodic.Chart.LocalizationCurvature
import OAI.Analysis.PDE.Dirichlet.Periodic.SmoothJetBounds
import OAI.Analysis.Normed.Function.Holder.C2HolderOperator

open Set Metric
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Elliptic OAI.Analysis.Normed.Function.Holder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance chartJetsFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance chartJetsFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance chartJetsSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance chartJetsSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem exists_smooth_jet_holder_bounds
    (η : E → ℝ) (hη : ContDiff ℝ 3 η) {S : Set E} (hS : IsCompact S)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ A : ℝ, 0 < A ∧ C2JetHolderBoundsOn η S α A := by
  obtain ⟨A₀,hA₀,ha₀,hh₀⟩ := smooth_jet_compact_holder_bound η (hη.of_le (by norm_num)) hS hα hα1
  have hD : ContDiff ℝ 2 (fderiv ℝ η) := hη.fderiv_right (by norm_num)
  obtain ⟨A₁,hA₁,ha₁,hh₁⟩ := smooth_jet_compact_holder_bound (fderiv ℝ η)
    (hD.of_le (by norm_num)) hS hα hα1
  obtain ⟨A₂,hA₂,ha₂,hh₂⟩ := smooth_jet_compact_holder_bound (fderiv ℝ (fderiv ℝ η))
    (hD.fderiv_right (by norm_num)) hS hα hα1
  refine ⟨A₀+A₁+A₂,by positivity,?_,?_,?_,?_,?_,?_⟩
  · exact fun x hx ↦ (ha₀ x hx).trans (by linarith)
  · exact fun x hx ↦ (ha₁ x hx).trans (by linarith)
  · exact fun x hx ↦ (ha₂ x hx).trans (by linarith)
  · intro x hx y hy
    simp_rw [dist_eq_norm] at hh₀
    exact (hh₀ x hx y hy).trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (norm_nonneg _) _))
  · intro x hx y hy
    simp_rw [dist_eq_norm] at hh₁
    exact (hh₁ x hx y hy).trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (norm_nonneg _) _))
  · intro x hx y hy
    simp_rw [dist_eq_norm] at hh₂
    exact (hh₂ x hx y hy).trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (norm_nonneg _) _))

theorem le_bounded_rpow {d R α : ℝ} (hd : 0 ≤ d) (hR : 0 ≤ R) (hdR : d ≤ R)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) : d ≤ (1+R)*d^α := by
  have hp := Real.rpow_nonneg hd α
  by_cases hsmall : d ≤ 1
  · have hh := Real.self_le_rpow_of_le_one hd hsmall hα1
    nlinarith
  · have hh : 1 ≤ d^α := Real.one_le_rpow (by linarith) hα
    nlinarith

omit [FiniteDimensional ℝ E] in
/-- Uniform first-derivative control for a composition. -/
theorem chart_first_derivative_bound {u : E → ℝ} {G : E → E}
    (hu : ContDiff ℝ 2 u) (hG : ContDiff ℝ 3 G) {x : E} {L N : ℝ}
    (hN : 0 ≤ N) (hu1 : ‖fderiv ℝ u (G x)‖ ≤ N)
    (hG1 : ‖fderiv ℝ G x‖ ≤ L) :
    ‖fderiv ℝ (fun z ↦ u (G z)) x‖ ≤ L*N := by
  have heq : fderiv ℝ (fun z ↦ u (G z)) x =
      (fderiv ℝ u (G x)).comp (fderiv ℝ G x) :=
    fderiv_comp x (hu.differentiable (by norm_num) _) (hG.differentiable (by norm_num) _)
  rw [heq]
  exact ((fderiv ℝ u (G x)).opNorm_comp_le (fderiv ℝ G x)).trans
    ((mul_le_mul hu1 hG1 (norm_nonneg _) hN).trans_eq (mul_comm _ _))

/-- The numerical chart constant depends only on chart and set bounds. -/
def chartJetConstant (L D α : ℝ) : ℝ :=
  1+L+(L^2+L)+(L^2*L^α+(3*L^2+L)*D)+L*D+(L^2+L)*D

theorem chartJetConstant_pos {L D α : ℝ} (hL : 0 ≤ L) (hD : 0 ≤ D) :
    0 < chartJetConstant L D α := by unfold chartJetConstant; positivity

/-- Analytic chart estimate before any closed-domain jet is supplied. -/
theorem chart_jet_holder_bounds_explicit
    {u : E → ℝ} {G : E → E} (hu : ContDiff ℝ 2 u) (hG : ContDiff ℝ 3 G)
    {S : Set E} (hconv : Convex ℝ S) {L D N α : ℝ}
    (hL : 0 ≤ L) (hD : 0 ≤ D) (hn : 0 ≤ N) (hα : 0 ≤ α)
    (hscale : ∀ x ∈ S, ∀ y ∈ S, ‖x-y‖ ≤ D*‖x-y‖^α)
    (huv : ∀ x ∈ S, ‖u (G x)‖ ≤ N)
    (hu1 : ∀ x ∈ S, ‖fderiv ℝ u (G x)‖ ≤ N)
    (hu2 : ∀ x ∈ S, ‖fderiv ℝ (gradient u) (G x)‖ ≤ N)
    (huα : ∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ (gradient u) (G x)-fderiv ℝ (gradient u) (G y)‖ ≤ N*‖G x-G y‖^α)
    (hG1 : ∀ x ∈ S, ‖fderiv ℝ G x‖ ≤ L)
    (hG2 : ∀ x ∈ S, ‖iteratedFDeriv ℝ 2 G x‖ ≤ L)
    (hG3 : ∀ x ∈ S, ‖iteratedFDeriv ℝ 3 G x‖ ≤ L) :
    C2JetHolderBoundsOn (fun x ↦ u (G x)) S α (chartJetConstant L D α*N) := by
  let T := L^2+L
  let H := L^2*L^α+(3*L^2+L)*D
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  let B := 1+L+T+H+L*D+T*D
  have hB : 0 < B := by dsimp [B]; positivity
  have hb₀ : 1 ≤ B := by dsimp [B]; nlinarith
  have hb₁ : L ≤ B := by dsimp [B]; nlinarith
  have hb₂ : T ≤ B := by dsimp [B]; nlinarith
  have hbH : H ≤ B := by dsimp [B]; nlinarith
  have hbD₁ : L*D ≤ B := by dsimp [B]; nlinarith
  have hbD₂ : T*D ≤ B := by dsimp [B]; nlinarith
  obtain ⟨hvn,hvh⟩ := chart_hessian_holder_bounded hu hG hconv hL hn hD hα hscale
    hu1 hu2 huα hG1 hG2 hG3
  let v := fun x ↦ u (G x)
  have hv : ContDiff ℝ 2 v := hu.comp (hG.of_le (by norm_num))
  have hv1 x (hx : x ∈ S) : ‖fderiv ℝ v x‖ ≤ L*N :=
    chart_first_derivative_bound hu hG hn (hu1 x hx) (hG1 x hx)
  have hv2 x (hx : x ∈ S) : ‖fderiv ℝ (fderiv ℝ v) x‖ ≤ T*N := by
    rw [← OAI.Analysis.PDE.Elliptic.norm_fderiv_gradient hv]
    exact hvn x hx
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro x hx
    apply (huv x hx).trans
    change N ≤ B*N
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hb₀ hn
  · exact fun x hx ↦ (hv1 x hx).trans (mul_le_mul_of_nonneg_right hb₁ hn)
  · exact fun x hx ↦ (hv2 x hx).trans (mul_le_mul_of_nonneg_right hb₂ hn)
  · intro x hx y hy
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ hv.differentiable (by norm_num) z) hv1 hconv hy hx
    apply h.trans
    calc
      _ ≤ (L*N)*(D*‖x-y‖^α) := mul_le_mul_of_nonneg_left (hscale x hx y hy) (by positivity)
      _ = (L*D)*N*‖x-y‖^α := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbD₁ hn)
        (Real.rpow_nonneg (norm_nonneg _) _)
  · intro x hx y hy
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ (hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z) hv2 hconv hy hx
    apply h.trans
    calc
      _ ≤ (T*N)*(D*‖x-y‖^α) := mul_le_mul_of_nonneg_left (hscale x hx y hy) (by positivity)
      _ = (T*D)*N*‖x-y‖^α := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbD₂ hn)
        (Real.rpow_nonneg (norm_nonneg _) _)
  · intro x hx y hy
    rw [← OAI.Analysis.PDE.Elliptic.norm_fderiv_gradient_sub hv]
    exact (hvh x hx y hy).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbH hn) (Real.rpow_nonneg (norm_nonneg _) _))

/-- A fixed C³ chart sends exact closed-domain jets to bounded local
Hölder jets. The constant is chosen before the solution or its norm. -/
theorem exists_chart_jet_holder_bound
    (G : E → E) (hG : ContDiff ℝ 3 G) {S Ω K : Set E}
    (hS : IsCompact S) (hconv : Convex ℝ S) (himage : MapsTo G S K)
    {hΩK : Ω ⊆ K} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ u : E → ℝ, ContDiff ℝ 2 u →
      ∀ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α,
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = u x) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) →
      C2JetHolderBoundsOn (fun x ↦ u (G x)) S α (B*‖U‖) := by
  have hDG : ContDiff ℝ 2 (fderiv ℝ G) := hG.fderiv_right (by norm_num)
  obtain ⟨L₁,hL₁⟩ := hS.exists_bound_of_continuousOn hDG.continuous.continuousOn
  obtain ⟨L₂,hL₂⟩ := hS.exists_bound_of_continuousOn
    (hG.continuous_iteratedFDeriv (by norm_num : (2 : ℕ∞ω) ≤ 3)).continuousOn
  obtain ⟨L₃,hL₃⟩ := hS.exists_bound_of_continuousOn
    (hG.continuous_iteratedFDeriv (by norm_num : (3 : ℕ∞ω) ≤ 3)).continuousOn
  let L := max L₁ 0+max L₂ 0+max L₃ 0+1
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hG1 x (hx : x ∈ S) : ‖fderiv ℝ G x‖ ≤ L := (hL₁ x hx).trans (by dsimp [L]; linarith [le_max_left L₁ 0,le_max_right L₂ 0,le_max_right L₃ 0])
  have hG2 x (hx : x ∈ S) : ‖iteratedFDeriv ℝ 2 G x‖ ≤ L := (hL₂ x hx).trans (by dsimp [L]; linarith [le_max_right L₁ 0,le_max_left L₂ 0,le_max_right L₃ 0])
  have hG3 x (hx : x ∈ S) : ‖iteratedFDeriv ℝ 3 G x‖ ≤ L := (hL₃ x hx).trans (by dsimp [L]; linarith [le_max_right L₁ 0,le_max_right L₂ 0,le_max_left L₃ 0])
  obtain ⟨R,hR⟩ := hS.exists_bound_of_continuousOn continuous_id.continuousOn
  let D := 1+2*max R 0
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hscale x (hx : x ∈ S) y (hy : y ∈ S) : ‖x-y‖ ≤ D*‖x-y‖^α := by
    apply le_bounded_rpow (norm_nonneg _) (by positivity) _ hα hα1
    exact (norm_sub_le x y).trans (by
      have hx' : ‖x‖ ≤ R := hR x hx
      have hy' : ‖y‖ ≤ R := hR y hy
      linarith [le_max_left R 0])
  refine ⟨chartJetConstant L D α,chartJetConstant_pos hL hD,?_⟩
  intro u hu U hU₀ hU₁ hU₂
  apply chart_jet_holder_bounds_explicit hu hG hconv hL hD (norm_nonneg U) hα hscale
  · intro x hx
    rw [← hU₀ ⟨G x,himage hx⟩]
    exact ((OAI.Analysis.Normed.Function.Holder.C2Holder.value U).norm_coe_le_norm _).trans (OAI.Analysis.Normed.Function.Holder.C2Holder.norm_value_le U)
  · intro x hx
    rw [← hU₁ ⟨G x,himage hx⟩]
    exact ((OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U).norm_coe_le_norm _).trans (OAI.Analysis.Normed.Function.Holder.C2Holder.norm_firstDerivative_le U)
  · intro x hx
    rw [OAI.Analysis.PDE.Elliptic.norm_fderiv_gradient hu,← hU₂ ⟨G x,himage hx⟩]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le (OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM U) _).trans (OAI.Analysis.Normed.Function.Holder.C2Holder.norm_hessianCLM_apply_le U)
  · intro x hx y hy
    rw [OAI.Analysis.PDE.Elliptic.norm_fderiv_gradient_sub hu,← hU₂ ⟨G x,himage hx⟩,← hU₂ ⟨G y,himage hy⟩]
    simpa only [Subtype.dist_eq,dist_eq_norm] using
      OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative_holder U ⟨G x,himage hx⟩ ⟨G y,himage hy⟩
  · exact hG1
  · exact hG2
  · exact hG3

end OAI.Analysis.PDE.Dirichlet
