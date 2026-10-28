import OAI.Analysis.PDE.Dirichlet.Periodic.Chart.LocalizationJets
import OAI.Analysis.PDE.Dirichlet.SchauderIsometry
import OAI.Analysis.PDE.Elliptic.Boundary.DifferentiatedOperator

noncomputable section
open Set Metric
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {m : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin m)
local instance lowerJetsFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance lowerJetsFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance lowerJetsSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance lowerJetsSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

omit [FiniteDimensional ℝ E] in
theorem second_fderiv_sub_fun (f g : E → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x : E) : fderiv ℝ (fderiv ℝ (fun y => f y-g y)) x =
      fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ g) x := by
  have hd : fderiv ℝ (fun y => f y-g y) = fun y => fderiv ℝ f y-fderiv ℝ g y := by
    funext y
    exact fderiv_sub (hf.differentiable (by norm_num) y) (hg.differentiable (by norm_num) y)
  rw [hd]
  exact fderiv_sub ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x)
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x)

/-- Lower jets after a fixed chart and fixed boundary lift use only the
original second-order norm, not the third derivative being estimated. -/
theorem exists_chart_remainder_lower_bound
    (e : X ≃ₗᵢ[ℝ] E) (G : E → E) (hG : ContDiff ℝ 3 G)
    (B₀ : E → ℝ) (hB₀ : ContDiff ℝ 3 B₀)
    {S Ω K : Set E} (hS : IsCompact S) (hconv : Convex ℝ S)
    (hGK : MapsTo G S K) {hΩK : Ω ⊆ K}
    {α R : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hR : 0 ≤ R) :
    ∃ V > 0, ∀ u : E → ℝ, ContDiff ℝ 2 u →
      ∀ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α, ‖U‖ ≤ R →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = u x) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) →
      ∀ x, e x ∈ S →
        ‖fderiv ℝ (((fun y => u y-B₀ y) ∘ G) ∘ e) x‖ ≤ V ∧
        ‖fderiv ℝ (fderiv ℝ (((fun y => u y-B₀ y) ∘ G) ∘ e)) x‖ ≤ V := by
  obtain ⟨C,hC,hjet⟩ := OAI.Analysis.PDE.Dirichlet.exists_chart_jet_holder_bound G hG hS hconv hGK
    (hΩK := hΩK) hα hα1
  obtain ⟨B,hB,hbackground⟩ := OAI.Analysis.PDE.Dirichlet.exists_smooth_jet_holder_bounds (B₀ ∘ G) (hB₀.comp hG) hS hα hα1
  refine ⟨C*R+B,by positivity,?_⟩
  intro u hu U hUn hU0 hU1 hU2 x hx
  have hj := hjet u hu U hU0 hU1 hU2
  have huc : ContDiff ℝ 2 (u ∘ G) := hu.comp (hG.of_le (by norm_num))
  have hbc : ContDiff ℝ 2 (B₀ ∘ G) := (hB₀.comp hG).of_le (by norm_num)
  have hrc : ContDiff ℝ 2 ((fun y => u y-B₀ y) ∘ G) :=
    (hu.sub (hB₀.of_le (by norm_num))).comp (hG.of_le (by norm_num))
  constructor
  · rw [OAI.Analysis.PDE.Dirichlet.norm_fderiv_isometry_comp e _ (hrc.differentiable (by norm_num))]
    change ‖fderiv ℝ (fun y => (u ∘ G) y-(B₀ ∘ G) y) (e x)‖ ≤ _
    have hd : fderiv ℝ (fun y => (u ∘ G) y-(B₀ ∘ G) y) (e x) =
        fderiv ℝ (u ∘ G) (e x)-fderiv ℝ (B₀ ∘ G) (e x) :=
      fderiv_sub (huc.differentiable (by norm_num) _) (hbc.differentiable (by norm_num) _)
    rw [hd]
    exact (norm_sub_le _ _).trans (add_le_add
      ((hj.first _ hx).trans (mul_le_mul_of_nonneg_left hUn hC.le)) (hbackground.first _ hx))
  · rw [OAI.Analysis.PDE.Dirichlet.norm_second_isometry_comp e _ hrc]
    change ‖fderiv ℝ (fderiv ℝ (fun y => (u ∘ G) y-(B₀ ∘ G) y)) (e x)‖ ≤ _
    rw [second_fderiv_sub_fun _ _ huc hbc]
    exact (norm_sub_le _ _).trans (add_le_add
      ((hj.second _ hx).trans (mul_le_mul_of_nonneg_left hUn hC.le)) (hbackground.second _ hx))

theorem coordinate_tangent_zero_of_trace (k : Fin m) (u : X → ℝ)
    (hu : ContDiff ℝ 1 u)
    (hz : ∀ x ∈ ball 0 (1/2 : ℝ), x k = 0 → u x = 0) :
    ∀ i, i ≠ k → ∀ x ∈ ball 0 (1/8 : ℝ), x k = 0 →
      OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1) x = 0 := by
  intro i hi x hx hxk
  let ell : X →L[ℝ] ℝ := (EuclideanSpace.proj k)
  apply directionalDerivative_zero_on_hyperplane isOpen_ball ell 0 hz
    ((ball_subset_ball (by norm_num)) hx) hxk _ (hu.differentiable one_ne_zero x)
  simp [ell, Ne.symm hi]

end OAI.Analysis.PDE.Elliptic
