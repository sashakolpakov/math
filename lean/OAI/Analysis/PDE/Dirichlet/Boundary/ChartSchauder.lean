import OAI.Analysis.PDE.Dirichlet.Boundary.ChartData
import OAI.Analysis.PDE.Dirichlet.ChartForcing
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.DriftJet
import OAI.Analysis.PDE.Dirichlet.Periodic.Chart.LocalizationUniform

open Set Metric InnerProductSpace Filter
open scoped Topology Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Elliptic OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

/-- A fixed curved chart gives a uniform small-error Schauder estimate.
All global Hölder coefficient and forcing fields are constructed from
their physical-domain bounds; the error uses the original stored jets. -/
theorem boundary_chart_schauder (hm : 3 ≤ m) (k : Fin m)
    (G P : E → E) (hG : ContDiff ℝ 3 G) (hP : ContDiff ℝ 3 P)
    {Ω K : Set E} {hΩK : Ω ⊆ K}
    (himage : MapsTo G (OAI.Analysis.PDE.Elliptic.closedCoordinateHalfPatch k 0 (1/2)) K)
    (hinv : ∀ z ∈ OAI.Analysis.PDE.Elliptic.closedCoordinateHalfPatch k 0 (1/2),
      (fun y => P (G y)) =ᶠ[𝓝 z] id)
    {C ell Λ N α : ℝ} (hC : 0 < C)
    (hDG : ‖fderiv ℝ G 0‖ ≤ C) (hDP : ‖fderiv ℝ P (G 0)‖ ≤ C)
    (hell : 0 < ell) (hΛ : 0 ≤ Λ) (hN : 0 ≤ N)
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ δ > 0, ∀ ε > 0, ∃ D > 0,
      ∀ A : E → E →L[ℝ] E, Continuous A →
      (∀ x ∈ K, (A x).toLinearMap.IsSymmetric) →
      (∀ x ∈ K, ∀ v : E, ell * ‖v‖^2 ≤ inner ℝ v (A x v)) →
      (∀ x ∈ K, ∀ v : E, inner ℝ v (A x v) ≤ Λ * ‖v‖^2) →
      (∀ x ∈ K, ‖A x‖ ≤ N) →
      (∀ x ∈ K, ∀ y ∈ K, ‖A x-A y‖ ≤ N * dist x y^α) →
      ∀ u : E → ℝ, ContDiff ℝ 3 u →
      (∀ z ∈ OAI.Analysis.PDE.Elliptic.closedCoordinateHalfPatch k 0 (1/2), z k = 0 → u (G z) = 0) →
      ∀ (F : E → ℝ) (B M : ℝ), 0 ≤ B → 0 ≤ M →
      (∀ x ∈ K, |F x| ≤ B) →
      (∀ x ∈ K, ∀ y ∈ K, |F x-F y| ≤ B * dist x y^α) →
      (∀ x ∈ K, |u x| ≤ M) →
      (∀ x ∈ K, OAI.Analysis.PDE.Elliptic.ellipticTrace A u x = F x) →
      ∀ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α,
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = u x) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) →
      SchauderJetBoundsOn (fun z => u (G z)) (OAI.Analysis.PDE.Elliptic.closedCoordinateHalfPatch k 0 δ)
        α (ε*‖U‖+D*(B+M)) := by
  let S := OAI.Analysis.PDE.Elliptic.closedCoordinateHalfPatch k (0 : E) (1/2)
  have hS0 : (0 : E) ∈ S := ⟨mem_closedBall_self (by norm_num), by simp⟩
  have hSc := OAI.Analysis.PDE.Elliptic.isCompact_closedCoordinateHalfPatch k (0 : E) (1/2)
  have hSv := OAI.Analysis.PDE.Elliptic.convex_closedCoordinateHalfPatch k (0 : E) (1/2)
  obtain ⟨CA, hCA, hfields⟩ := OAI.Analysis.PDE.Schauder.exists_chart_matrix_holder_fields G P hG
    (hP.of_le (by norm_num)) ⟨0, hS0⟩ hSc hSv (coordinate_half_patch_diameter k) hα.le hα1.le
  obtain ⟨CF, hCF, hforcing⟩ := exists_chart_raw_forcing_extension G
    (hG.of_le (by norm_num)) ⟨0, hS0⟩ hSc hSv hα
  let ell' := ell / C^2
  let Λ' := Λ * C^2
  have hell' : 0 < ell' := div_pos hell (sq_pos_of_pos hC)
  have hΛ' : 0 ≤ Λ' := mul_nonneg hΛ (sq_nonneg C)
  obtain ⟨r, hr, hrone, hrnear, δ, hδ, hlocal⟩ :=
    OAI.Analysis.PDE.Schauder.uniform_boundary_local_jet_schauder_with_drift hm k hα hα1 hell' hΛ'
      (mul_nonneg hCA.le hN) (mul_nonneg hCA.le hN) (by norm_num : (0 : ℝ) < 1/8)
  have hrK : r * Real.sqrt Λ' < (1/2 : ℝ)/2 := by
    have hlt : r * (Real.sqrt Λ' + 1) < (1/8 : ℝ) :=
      (lt_div_iff₀ (by positivity)).mp hrnear
    nlinarith
  have himage' : MapsTo G ({x : E | 0 ≤ x k} ∩ closedBall 0 (1/2)) K := by
    intro x hx
    exact himage ⟨hx.2, hx.1⟩
  obtain ⟨CH, hCH, hcutoff⟩ := exists_uniform_halfspace_equiv_chart_hessian_bound
    k G hG (by norm_num : (0 : ℝ) < 1/2) hr (Real.sqrt_nonneg Λ') hrK
      himage' (hΩK := hΩK) hα.le hα1.le
  have hnear (z : E) (hz : z ∈ ball 0 (1/8)) (hzk : 0 ≤ z k) : z ∈ S := by
    exact ⟨(closedBall_subset_closedBall (by norm_num)) (ball_subset_closedBall hz), hzk⟩
  refine ⟨δ/2, half_pos hδ, ?_⟩
  intro ε hε
  obtain ⟨D₀, hD₀, hestimate⟩ := hlocal (ε/(CH+1)) (div_pos hε (by positivity))
  let D := D₀*(CF+1)+1
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro A hA hAs hAl hAu hAn hAh u hu hz F B M hB hM hFn hFh hun heq U hU0 hU1 hU2
  obtain ⟨A', b, hA'n, hbn, hA', hb⟩ := hfields A hA N hN
    (fun z hz => hAn (G z) (himage hz)) (by
      intro x hx y hy
      simpa only [dist_eq_norm] using hAh (G x) (himage hx) (G y) (himage hy))
  obtain ⟨F', hF', hF'n⟩ := hforcing K himage B hB F hFn hFh
  have h0K : G 0 ∈ K := himage hS0
  have hji := (OAI.Analysis.PDE.Elliptic.chart_jacobians_inverse
    (hP.differentiable (by norm_num) (G 0)) (hG.differentiable (by norm_num) 0) (hinv 0 hS0)).1
  have helliptic := chart_matrix_ellipticity (fderiv ℝ P (G 0)) (fderiv ℝ G 0) (A (G 0))
    hji (hAs _ h0K) hC hDP hDG hell hΛ (hAl _ h0K) (hAu _ h0K)
  rw [← hA' 0 hS0] at helliptic
  obtain ⟨L, hLplane, hL, hLi, hLestimate⟩ := hestimate A' hA'n 0 (by simp)
    helliptic.1 helliptic.2.1 helliptic.2.2
  have hcut := (hcutoff L hL hLplane u (hu.of_le (by norm_num)) U hU0 hU1 hU2).2
  have hw : ContDiff ℝ 3 (fun z => u (G z)) := hu.comp hG
  have hflat := hLestimate b hbn (fun z => u (G z)) hw
    (fun z hzn hzk => hz z (hnear z hzn hzk.ge) hzk) F' (CH*‖U‖) M
    (mul_nonneg hCH.le (norm_nonneg U)) hM
    (fun z hzn hzk => hun (G z) (himage (hnear z hzn hzk))) (by
      intro z hzn hzk
      have hzs := hnear z hzn hzk
      rw [OAI.Analysis.PDE.Schauder.chart_nondivergence_equation A G P u (hG.of_le (by norm_num))
        (hP.of_le (by norm_num)) (hu.of_le (by norm_num)) A' b z
        (hAs _ (himage hzs)) (hinv z hzs) (hA' z hzs) (hb z hzs),
        hF' z hzs, heq _ (himage hzs)]) (by simpa only [zero_add] using hcut)
  have hsmall : ε/(CH+1) * (CH*‖U‖) ≤ ε*‖U‖ := by
    have hc : CH/(CH+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    calc
      _ = (CH/(CH+1))*(ε*‖U‖) := by ring
      _ ≤ 1*(ε*‖U‖) := mul_le_mul_of_nonneg_right hc (mul_nonneg hε.le (norm_nonneg U))
      _ = _ := one_mul _
  have hforce : D₀*(‖F'‖+M) ≤ D*(B+M) := by
    have hbase : ‖F'‖+M ≤ (CF+1)*(B+M) := by nlinarith
    have hDbase : D₀*(CF+1) ≤ D := by dsimp only [D]; linarith
    exact (mul_le_mul_of_nonneg_left hbase hD₀.le).trans
      ((by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hDbase (add_nonneg hB hM)))
  have htotal : ε/(CH+1)*(CH*‖U‖)+D₀*(‖F'‖+M) ≤ ε*‖U‖+D*(B+M) :=
    add_le_add hsmall hforce
  have hvalue : M ≤ ε*‖U‖+D*(B+M) := by
    have hD1 : 1 ≤ D := by
      have hp : 0 ≤ D₀*(CF+1) := mul_nonneg hD₀.le (by positivity)
      dsimp only [D]
      linarith
    nlinarith [mul_nonneg hε.le (norm_nonneg U)]
  have hδnear (z : E) (hzn : z ∈ OAI.Analysis.PDE.Elliptic.closedCoordinateHalfPatch k 0 (δ/2)) : z ∈ ball 0 δ :=
    (closedBall_subset_ball (by linarith)) hzn.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hzn
    exact ((hflat.1 z (hδnear z hzn) hzn.2).1).trans hvalue
  · intro z hzn
    exact ((hflat.1 z (hδnear z hzn) hzn.2).2.1).trans htotal
  · intro z hzn
    exact ((hflat.1 z (hδnear z hzn) hzn.2).2.2).trans htotal
  · intro x hx y hy
    exact (hflat.2 x (hδnear x hx) hx.2 y (hδnear y hy) hy.2).trans
      (mul_le_mul_of_nonneg_right htotal (Real.rpow_nonneg (norm_nonneg _) _))

end OAI.Analysis.PDE.Dirichlet
