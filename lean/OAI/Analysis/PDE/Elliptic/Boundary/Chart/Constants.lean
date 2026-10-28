import OAI.Analysis.PDE.Elliptic.Boundary.NormalizedChart
import OAI.Analysis.PDE.Elliptic.Boundary.InversePullback

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter
open scoped Topology

section General
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_C3_derivative_bounds {f : E → F} (hf : ContDiff ℝ 3 f)
    {K : Set E} (hK : IsCompact K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ K,
      ‖fderiv ℝ f x‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 f x‖ ≤ C ∧ ‖iteratedFDeriv ℝ 3 f x‖ ≤ C := by
  have hc (j : ℕ) (hj : j ≤ 3) : Continuous (fun x => ‖iteratedFDeriv ℝ j f x‖) :=
    continuous_iff_continuousAt.mpr fun x =>
      (hf.contDiffAt.continuousAt_iteratedFDeriv (by exact_mod_cast hj)).norm
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn (hc 1 (by norm_num)).continuousOn
  obtain ⟨C2, hC2⟩ := hK.exists_bound_of_continuousOn (hc 2 (by norm_num)).continuousOn
  obtain ⟨C3, hC3⟩ := hK.exists_bound_of_continuousOn (hc 3 (by norm_num)).continuousOn
  let C := max 1 (max C1 (max C2 C3))
  have h1 : C1 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have h2 : C2 ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h3 : C3 ≤ C := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨C, le_max_left _ _, ?_⟩
  intro x hx
  refine ⟨?_, ?_, ?_⟩
  · exact (by simpa [norm_iteratedFDeriv_one] using hC1 x hx : ‖fderiv ℝ f x‖ ≤ C1).trans h1
  · exact (by simpa using hC2 x hx : ‖iteratedFDeriv ℝ 2 f x‖ ≤ C2).trans h2
  · exact (by simpa using hC3 x hx : ‖iteratedFDeriv ℝ 3 f x‖ ≤ C3).trans h3

end General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem chart_jacobians_inverse {P G : E → E} {z : E}
    (hP : DifferentiableAt ℝ P (G z)) (hG : DifferentiableAt ℝ G z)
    (hinv : (fun y => P (G y)) =ᶠ[𝓝 z] id) :
    (fderiv ℝ P (G z)).comp (fderiv ℝ G z) = ContinuousLinearMap.id ℝ E ∧
    (fderiv ℝ G z).comp (fderiv ℝ P (G z)) = ContinuousLinearMap.id ℝ E := by
  have hd := hinv.fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (P ∘ G) z = fderiv ℝ id z at hd
  rw [(hP.hasFDerivAt.comp z hG.hasFDerivAt).fderiv] at hd
  have hleft : (fderiv ℝ P (G z)).comp (fderiv ℝ G z) = ContinuousLinearMap.id ℝ E := by
    simpa using hd
  exact ⟨hleft, clm_left_inverse_comm (fderiv ℝ G z) (fderiv ℝ P (G z)) hleft⟩

theorem exists_bounded_normalized_chart {r : E → ℝ} (hr : ContDiff ℝ 3 r)
    (x : E) (hg : fderiv ℝ r x ≠ 0) {U : Set E} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ (v : E) (c C : ℝ) (G P : E → E), ‖v‖ = 1 ∧ 0 < c ∧ 1 ≤ C ∧
      ContDiff ℝ 3 G ∧ ContDiff ℝ 3 P ∧ G 0 = x ∧
      ∀ z ∈ Metric.closedBall 0 2,
        G z ∈ U ∧ (fun y => P (G y)) =ᶠ[𝓝 z] id ∧
        r (G z) - r x = -c * inner ℝ v z ∧
        ‖fderiv ℝ G z‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 G z‖ ≤ C ∧
        ‖iteratedFDeriv ℝ 3 G z‖ ≤ C ∧ ‖fderiv ℝ P (G z)‖ ≤ C := by
  obtain ⟨v, c, G, P, hv, hc, hG, hP, hG0, hchart⟩ := exists_doubled_boundary_chart hr x hg hU hxU
  obtain ⟨C1, hC1, hB1⟩ := compact_C3_derivative_bounds hG (isCompact_closedBall (0 : E) 2)
  obtain ⟨C2, hC2, hB2⟩ := compact_C3_derivative_bounds hP
    ((isCompact_closedBall (0 : E) 2).image hG.continuous)
  refine ⟨v, c, max C1 C2, G, P, hv, hc, hC1.trans (le_max_left _ _), hG, hP, hG0, ?_⟩
  intro z hz
  have h1 := hB1 z hz
  have h2 := hB2 (G z) ⟨z, hz, rfl⟩
  exact ⟨(hchart z hz).1, (hchart z hz).2.1, (hchart z hz).2.2,
    h1.1.trans (le_max_left _ _), h1.2.1.trans (le_max_left _ _),
    h1.2.2.trans (le_max_left _ _), h2.1.trans (le_max_right _ _)⟩

end OAI.Analysis.PDE.Elliptic
