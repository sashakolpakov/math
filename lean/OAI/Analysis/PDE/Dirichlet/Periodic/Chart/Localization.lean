import OAI.Analysis.PDE.Dirichlet.Periodic.Chart.LocalizationJets
import OAI.Analysis.PDE.Dirichlet.Periodic.Chart.LocalizationSupport
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.SupportBounds

open Set Metric
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local instance chartLocalFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance chartLocalFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance chartLocalSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance chartLocalSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- Bounded chart localization on a closed convex region. The fixed
constant is independent of the smooth solution and of all its values
outside the physical jet domain. -/
theorem exists_cutoff_chart_hessian_bound
    (G : E → E) (hG : ContDiff ℝ 3 G) (η : E → ℝ) (hη : ContDiff ℝ 3 η)
    (T : Set E) (hTc : IsClosed T) (hTv : Convex ℝ T)
    (x₀ : E) {r R : ℝ} (hrR : r < R) (hs : tsupport η ⊆ closedBall x₀ r)
    {Ω K : Set E} (himage : MapsTo G (T ∩ closedBall x₀ R) K)
    {hΩK : Ω ⊆ K} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : E → ℝ, ContDiff ℝ 2 u →
      ∀ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α,
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = u x) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) →
      (∀ x ∈ T, ‖fderiv ℝ (fderiv ℝ (fun z ↦ η z*u (G z))) x‖ ≤ C*‖U‖) ∧
      (∀ x ∈ T, ∀ y ∈ T,
        ‖fderiv ℝ (fderiv ℝ (fun z ↦ η z*u (G z))) x-
          fderiv ℝ (fderiv ℝ (fun z ↦ η z*u (G z))) y‖ ≤ C*‖U‖*‖x-y‖^α) := by
  let S := T ∩ closedBall x₀ R
  have hSc : IsCompact S := (isCompact_closedBall x₀ R).inter_left hTc
  have hSv : Convex ℝ S := hTv.inter (convex_closedBall x₀ R)
  obtain ⟨A,hA,hηA⟩ := exists_smooth_jet_holder_bounds η hη hSc hα hα1
  obtain ⟨B,hB,hGB⟩ := exists_chart_jet_holder_bound G hG hSc hSv himage
    (hΩK := hΩK) hα hα1
  let C := 8*A*B+8*A*B/(R-r)^α
  have hgap : 0 < (R-r)^α := Real.rpow_pos_of_pos (sub_pos.mpr hrR) _
  have hC : 0 < C := by dsimp [C]; positivity
  have hC4 : 4*A*B ≤ C := by
    have hab : 0 ≤ A*B := mul_nonneg hA.le hB.le
    have hq : 0 ≤ 8*A*B/(R-r)^α := by positivity
    dsimp [C]
    nlinarith
  refine ⟨C,hC,?_⟩
  intro u hu U hU₀ hU₁ hU₂
  let v := fun z ↦ u (G z)
  let f := fun z ↦ η z*v z
  let F := fderiv ℝ (fderiv ℝ f)
  have hv : ContDiff ℝ 2 v := hu.comp (hG.of_le (by norm_num))
  have hvB := hGB u hu U hU₀ hU₁ hU₂
  obtain ⟨hFn,hFh⟩ := cutoff_hessian_bounds_on η v (hη.of_le (by norm_num)) hv
    hA.le (mul_nonneg hB.le (norm_nonneg U)) hηA hvB
  have hFzero x (hx : x ∉ closedBall x₀ r) : F x = 0 := by
    apply OAI.Analysis.PDE.Schauder.hessian_zero_outside_support f x
    exact fun h ↦ hx (hs (tsupport_mul_subset_left h))
  have hFnT x (hxT : x ∈ T) : ‖F x‖ ≤ (4*A*B)*‖U‖ := by
    by_cases hx : x ∈ closedBall x₀ R
    · exact (hFn x ⟨hxT,hx⟩).trans_eq (by ring)
    · rw [hFzero x (fun h ↦ hx (closedBall_subset_closedBall hrR.le h)),norm_zero]
      positivity
  have hFhT := holder_on_of_support_separated F T x₀ hrR hα
    (C := (8*A*B)*‖U‖) (M := (4*A*B)*‖U‖) (by positivity) (by positivity)
    (fun x _ hx ↦ hFzero x hx) hFnT (by
      intro x hx y hy
      exact (hFh x hx y hy).trans_eq (by ring))
  constructor
  · intro x hx
    exact (hFnT x hx).trans (mul_le_mul_of_nonneg_right hC4 (norm_nonneg U))
  · intro x hx y hy
    exact (hFhT x hx y hy).trans_eq (by dsimp [C]; ring)

/-- The precise closed-halfspace form used by the boundary Schauder
estimate, with the original Hölder exponent and a solution-independent constant. -/
theorem exists_halfspace_cutoff_chart_hessian_bound {m : ℕ} (k : Fin m)
    (G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (hG : ContDiff ℝ 3 G)
    (η : EuclideanSpace ℝ (Fin m) → ℝ) (hη : ContDiff ℝ 3 η)
    (x₀ : EuclideanSpace ℝ (Fin m)) {r R : ℝ} (hrR : r < R)
    (hs : tsupport η ⊆ closedBall x₀ r)
    {Ω K : Set (EuclideanSpace ℝ (Fin m))}
    (himage : MapsTo G ({x | 0 ≤ x k} ∩ closedBall x₀ R) K)
    {hΩK : Ω ⊆ K} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : EuclideanSpace ℝ (Fin m) → ℝ, ContDiff ℝ 2 u →
      ∀ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α,
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = u x) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) →
      (∀ x, 0 ≤ x k → ‖fderiv ℝ (fderiv ℝ (fun z ↦ η z*u (G z))) x‖ ≤ C*‖U‖) ∧
      (∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ (fun z ↦ η z*u (G z))) x-
          fderiv ℝ (fderiv ℝ (fun z ↦ η z*u (G z))) y‖ ≤ C*‖U‖*‖x-y‖^α) := by
  have hTc : IsClosed ({x : EuclideanSpace ℝ (Fin m) | 0 ≤ x k}) :=
    isClosed_le continuous_const (by fun_prop)
  have hTv : Convex ℝ ({x : EuclideanSpace ℝ (Fin m) | 0 ≤ x k}) := by
    intro x hx y hy a b ha hb _
    change 0 ≤ (a • x+b • y) k
    simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  exact exists_cutoff_chart_hessian_bound G hG η hη _ hTc hTv x₀ hrR hs himage hα hα1

end OAI.Analysis.PDE.Dirichlet
