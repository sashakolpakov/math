import OAI.Analysis.PDE.Dirichlet.Periodic.Chart.LocalizationUniformInteriorJets
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.ScaledEquiv

open Set Metric
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

local instance interiorCutoffFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance interiorCutoffFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance interiorCutoffSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance interiorCutoffSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem normalized_affine_mapsTo_ball (L : E →L[ℝ] E) (x₀ : E)
    {r P ρ : ℝ} (hr : 0 ≤ r) (hP : 0 ≤ P) (hL : ‖L‖ ≤ P)
    (hscale : 2*r*P < ρ) :
    MapsTo (fun z ↦ x₀+L (r • z)) (closedBall 0 2) (ball x₀ ρ) := by
  intro z hz
  have hz' : ‖z‖ ≤ 2 := by simpa only [mem_closedBall,dist_zero_right] using hz
  rw [mem_ball,dist_eq_norm,add_sub_cancel_left]
  calc
    _ ≤ ‖L‖*‖r • z‖ := L.le_opNorm _
    _ = ‖L‖*(r*‖z‖) := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
    _ ≤ P*(r*2) := mul_le_mul hL (mul_le_mul_of_nonneg_left hz' hr)
      (mul_nonneg hr (norm_nonneg _)) hP
    _ = 2*r*P := by ring
    _ < ρ := hscale

theorem exists_radial_cutoff_jet_bound
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : E → ℝ, ContDiff ℝ 2 v → ∀ N : ℝ, 0 ≤ N →
      C2JetHolderBoundsOn v (closedBall 0 2) α N →
      (∀ x, ‖fderiv ℝ (fderiv ℝ (fun z ↦ OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z*v z)) x‖ ≤ C*N) ∧
      (∀ x y,
        ‖fderiv ℝ (fderiv ℝ (fun z ↦ OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z*v z)) x-
          fderiv ℝ (fderiv ℝ (fun z ↦ OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z*v z)) y‖ ≤ C*N*‖x-y‖^α) := by
  let η : E → ℝ := OAI.Analysis.PDE.Schauder.radialCutoff (1/2)
  have hη : ContDiff ℝ 3 η := (OAI.Analysis.PDE.Schauder.contDiff_radialCutoff _).of_le (by simp)
  have hs : tsupport η ⊆ closedBall (0:E) 1 := by
    have hh : tsupport (OAI.Analysis.PDE.Schauder.radialCutoff (1/2) : E → ℝ) ⊆ closedBall 0 (2*(1/2)) :=
      OAI.Analysis.PDE.Schauder.tsupport_radialCutoff_subset (by norm_num)
    simpa only [show (2:ℝ)*(1/2)=1 by norm_num] using hh
  obtain ⟨A,hA,hηA⟩ := exists_smooth_jet_holder_bounds η hη (isCompact_closedBall 0 2) hα hα1
  refine ⟨16*A,by positivity,?_⟩
  intro v hv N hN hvN
  let f := fun z ↦ η z*v z
  let F := fderiv ℝ (fderiv ℝ f)
  obtain ⟨hFn,hFh⟩ := cutoff_hessian_bounds_on η v (hη.of_le (by norm_num)) hv hA.le hN hηA hvN
  have hFzero x (hx : x ∉ closedBall (0:E) 1) : F x = 0 := by
    apply OAI.Analysis.PDE.Schauder.hessian_zero_outside_support f x
    exact fun h ↦ hx (hs (tsupport_mul_subset_left h))
  have hFnT x : ‖F x‖ ≤ 4*A*N := by
    by_cases hx : x ∈ closedBall (0:E) 2
    · exact hFn x hx
    · rw [hFzero x (fun h ↦ hx (closedBall_subset_closedBall (by norm_num : (1:ℝ)≤2) h)),norm_zero]
      positivity
  have hFhT := holder_on_of_support_separated F univ 0 (r := 1) (R := 2) (by norm_num) hα
    (C := 8*A*N) (M := 4*A*N) (by positivity) (by positivity)
    (fun x _ hx ↦ hFzero x hx) (fun x _ ↦ hFnT x)
    (fun x hx y hy ↦ hFh x hx.2 y hy.2)
  constructor
  · intro x
    exact (hFnT x).trans (by nlinarith [mul_nonneg hA.le hN])
  · intro x y
    have hh := hFhT x (mem_univ _) y (mem_univ _)
    norm_num only [show (2:ℝ)-1=1 by norm_num,Real.one_rpow,div_one] at hh
    exact hh.trans_eq (by ring)

/-- A single cutoff constant works at every center and for every affine
linear part with the given norm bound. Only its radius-two image is used. -/
theorem exists_uniform_affine_cutoff_hessian_bound
    {Ω Kset : Set E} {hΩK : Ω ⊆ Kset} {α P : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hP : 0 ≤ P) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : E →L[ℝ] E) (b : E), ‖A‖ ≤ P →
      MapsTo (fun z ↦ b+A z) (closedBall 0 2) Kset →
      ∀ u : E → ℝ, ContDiff ℝ 2 u → ∀ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α,
      (∀ x : Kset, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = u x) →
      (∀ x : Kset, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x) →
      (∀ x : Kset, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) →
      (∀ x, ‖fderiv ℝ (fderiv ℝ (fun z ↦ OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z*u (b+A z))) x‖ ≤ C*‖U‖) ∧
      (∀ x y, ‖fderiv ℝ (fderiv ℝ (fun z ↦ OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z*u (b+A z))) x-
        fderiv ℝ (fderiv ℝ (fun z ↦ OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z*u (b+A z))) y‖ ≤ C*‖U‖*‖x-y‖^α) := by
  obtain ⟨D,hD,hcut⟩ := exists_radial_cutoff_jet_bound (m := m) hα hα1
  have hQ : 0 < affineJetConstant P α := (affineJetConstant_bounds hP).1
  refine ⟨D*(6*affineJetConstant P α),by positivity,?_⟩
  intro A b hA himage u hu U hU0 hU1 hU2
  have hjet := stored_jet_affine_uniform hα hα1 hP u hu U hU0 hU1 hU2 A b hA himage
  have hh := hcut (fun z ↦ u (b+A z)) (hu.comp (contDiff_const.add A.contDiff))
    (6*(affineJetConstant P α*‖U‖)) (by positivity) hjet
  simpa only [mul_assoc] using hh

/-- In particular, the same bound is uniform in all scales `0 < r ≤ 1`
and all centers, when the linear map has a fixed norm bound. -/
theorem exists_uniform_interior_normalized_cutoff_hessian_bound
    {Ω Kset : Set E} {hΩK : Ω ⊆ Kset} {α P : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hP : 0 ≤ P) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : E →L[ℝ] E) (x₀ : E) (r : ℝ),
      ‖L‖ ≤ P → 0 < r → r ≤ 1 →
      MapsTo (fun z ↦ x₀+L (r • z)) (closedBall 0 2) Kset →
      ∀ u : E → ℝ, ContDiff ℝ 2 u → ∀ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α,
      (∀ x : Kset, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = u x) →
      (∀ x : Kset, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x) →
      (∀ x : Kset, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) →
      (∀ x, ‖fderiv ℝ (fderiv ℝ (fun z ↦ OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z*u (x₀+L (r • z)))) x‖ ≤ C*‖U‖) ∧
      (∀ x y, ‖fderiv ℝ (fderiv ℝ (fun z ↦ OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z*u (x₀+L (r • z)))) x-
        fderiv ℝ (fderiv ℝ (fun z ↦ OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z*u (x₀+L (r • z)))) y‖ ≤ C*‖U‖*‖x-y‖^α) := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_affine_cutoff_hessian_bound
    (hΩK := hΩK) hα hα1 hP
  refine ⟨C,hC,?_⟩
  intro L x₀ r hL hr hr1 himage
  have hn : ‖r • L‖ ≤ P := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left hL hr.le).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hr1 hP)
  have hm : MapsTo (fun z ↦ x₀+(r • L) z) (closedBall 0 2) Kset := by
    simpa only [smul_apply,map_smul] using himage
  simpa only [smul_apply,map_smul] using hbound (r • L) x₀ hn hm

end OAI.Analysis.PDE.Dirichlet
