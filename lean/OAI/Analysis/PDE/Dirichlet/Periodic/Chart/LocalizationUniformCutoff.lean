import OAI.Analysis.PDE.Dirichlet.Periodic.Chart.Localization
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.ScaledEquiv

open Set Metric
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Schauder

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

local instance uniformCutoffFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance uniformCutoffFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance uniformCutoffSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance uniformCutoffSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- One fixed cutoff converts jet bounds on the halfball of radius two
into Hessian bounds on the entire closed halfspace. -/
theorem exists_halfspace_radial_cutoff_jet_bound (k : Fin m)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : E → ℝ, ContDiff ℝ 2 v → ∀ N : ℝ, 0 ≤ N →
      C2JetHolderBoundsOn v ({x | 0 ≤ x k} ∩ closedBall 0 2) α N →
      (∀ x, 0 ≤ x k →
        ‖fderiv ℝ (fderiv ℝ (fun z ↦ OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z*v z)) x‖ ≤ C*N) ∧
      (∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ (fun z ↦ OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z*v z)) x-
          fderiv ℝ (fderiv ℝ (fun z ↦ OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z*v z)) y‖ ≤ C*N*‖x-y‖^α) := by
  let T : Set E := {x | 0 ≤ x k}
  let S := T ∩ closedBall (0 : E) 2
  let η : E → ℝ := OAI.Analysis.PDE.Schauder.radialCutoff (1/2)
  have hTc : IsClosed T := isClosed_le continuous_const (by fun_prop)
  have hSc : IsCompact S := (isCompact_closedBall (0 : E) 2).inter_left hTc
  have hη : ContDiff ℝ 3 η := (OAI.Analysis.PDE.Schauder.contDiff_radialCutoff _).of_le (by simp)
  have hs : tsupport η ⊆ closedBall (0 : E) 1 := by
    have hh : tsupport (OAI.Analysis.PDE.Schauder.radialCutoff (1/2) : E → ℝ) ⊆ closedBall 0 (2*(1/2)) :=
      OAI.Analysis.PDE.Schauder.tsupport_radialCutoff_subset (by norm_num)
    simpa only [show (2:ℝ)*(1/2)=1 by norm_num] using hh
  obtain ⟨A,hA,hηA⟩ := exists_smooth_jet_holder_bounds η hη hSc hα hα1
  refine ⟨16*A,by positivity,?_⟩
  intro v hv N hN hvN
  let f := fun z ↦ η z*v z
  let F := fderiv ℝ (fderiv ℝ f)
  obtain ⟨hFn,hFh⟩ := cutoff_hessian_bounds_on η v (hη.of_le (by norm_num)) hv
    hA.le hN hηA hvN
  have hFzero x (hx : x ∉ closedBall (0 : E) 1) : F x = 0 := by
    apply OAI.Analysis.PDE.Schauder.hessian_zero_outside_support f x
    exact fun h ↦ hx (hs (tsupport_mul_subset_left h))
  have hFnT x (hxT : x ∈ T) : ‖F x‖ ≤ 4*A*N := by
    by_cases hx : x ∈ closedBall (0 : E) 2
    · exact hFn x ⟨hxT,hx⟩
    · rw [hFzero x (fun h ↦ hx (closedBall_subset_closedBall (by norm_num : (1:ℝ)≤2) h)),norm_zero]
      positivity
  have hFhT := holder_on_of_support_separated F T 0 (r := 1) (R := 2) (by norm_num) hα
    (C := 8*A*N) (M := 4*A*N) (by positivity) (by positivity)
    (fun x _ hx ↦ hFzero x hx) hFnT hFh
  constructor
  · intro x hx
    exact (hFnT x hx).trans (by nlinarith [mul_nonneg hA.le hN])
  · intro x hx y hy
    have hh := hFhT x hx y hy
    norm_num only [show (2:ℝ)-1=1 by norm_num, Real.one_rpow, div_one] at hh
    exact hh.trans_eq (by ring)

end OAI.Analysis.PDE.Dirichlet
