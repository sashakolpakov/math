import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Recovery
import OAI.Analysis.PDE.Elliptic.Boundary.Curvature

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem hessianCongruence_add (Q H K : E →L[ℝ] E) :
    hessianCongruence Q (H + K) = hessianCongruence Q H + hessianCongruence Q K := by
  ext x; simp [hessianCongruence]

theorem hessianCongruence_inverse (Q J A : E →L[ℝ] E)
    (hJQ : J.comp Q = ContinuousLinearMap.id ℝ E) :
    hessianCongruence Q (hessianCongruence J A) = A := by
  have hadj : Q.adjoint.comp J.adjoint = ContinuousLinearMap.id ℝ E := by
    simpa [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
      congrArg (ContinuousLinearMap.adjoint : (E →L[ℝ] E) → _) hJQ
  have ha : Q.adjoint * J.adjoint = 1 := hadj
  have hj : J * Q = 1 := hJQ
  change Q.adjoint * ((J.adjoint * (A * J)) * Q) = A
  calc
    _ = (Q.adjoint * J.adjoint) * A * (J * Q) := by noncomm_ring
    _ = A := by rw [ha, hj, one_mul, mul_one]

theorem hessianCongruence_variation (J K A : E →L[ℝ] E) :
    ‖hessianCongruence J A - hessianCongruence K A‖ ≤
      ‖J - K‖ * ‖A‖ * ‖J‖ + ‖K‖ * ‖A‖ * ‖J - K‖ := by
  have hid : hessianCongruence J A - hessianCongruence K A =
      (J.adjoint - K.adjoint) * A * J + K.adjoint * A * (J - K) := by
    change J.adjoint * (A * J) - K.adjoint * (A * K) = _
    noncomm_ring
  rw [hid]
  have h1 := (norm_mul_le ((J.adjoint - K.adjoint) * A) J).trans
    (mul_le_mul_of_nonneg_right (norm_mul_le (J.adjoint - K.adjoint) A) (norm_nonneg _))
  have h2 := (norm_mul_le (K.adjoint * A) (J - K)).trans
    (mul_le_mul_of_nonneg_right (norm_mul_le K.adjoint A) (norm_nonneg _))
  have hn : ‖J.adjoint - K.adjoint‖ = ‖J - K‖ := by
    rw [← map_sub, ContinuousLinearMap.adjoint.norm_map]
  simpa only [hn, ContinuousLinearMap.adjoint.norm_map] using
    (norm_add_le _ _).trans (add_le_add h1 h2)

theorem chart_hessian_change_error_bound {u : E → ℝ} {G : E → E} {S : Set E} {V : ℝ}
    (hu : ContDiff ℝ 2 u) (hG : ContDiff ℝ 3 G) (hS : Convex ℝ S) (hV : 0 ≤ V)
    (hu1 : ∀ z ∈ S, ‖fderiv ℝ u (G z)‖ ≤ V)
    (hu2 : ∀ z ∈ S, ‖fderiv ℝ (gradient u) (G z)‖ ≤ V)
    (hG1 : ∀ z ∈ S, ‖fderiv ℝ G z‖ ≤ V)
    (hG2 : ∀ z ∈ S, ‖iteratedFDeriv ℝ 2 G z‖ ≤ V)
    (hG3 : ∀ z ∈ S, ‖iteratedFDeriv ℝ 3 G z‖ ≤ V)
    {z z' : E} (hz : z ∈ S) (hz' : z' ∈ S) (Q : E →L[ℝ] E)
    (hQ : ‖Q‖ ≤ V) (hJQ : (fderiv ℝ G z).comp Q = ContinuousLinearMap.id ℝ E) :
    ‖(fderiv ℝ (gradient u) (G z) - fderiv ℝ (gradient u) (G z')) -
      hessianCongruence Q (fderiv ℝ (gradient (fun y => u (G y))) z -
        fderiv ℝ (gradient (fun y => u (G y))) z')‖ ≤
      (3 * V ^ 5 + V ^ 4) * ‖z - z'‖ := by
  let J := fderiv ℝ G z
  let K := fderiv ℝ G z'
  let A := fderiv ℝ (gradient u) (G z)
  let B := fderiv ℝ (gradient u) (G z')
  have hid : (A - B) -
      hessianCongruence Q (fderiv ℝ (gradient (fun y => u (G y))) z -
        fderiv ℝ (gradient (fun y => u (G y))) z') =
      hessianCongruence Q ((hessianCongruence K B - hessianCongruence J B) -
        (chartCurvature u G z - chartCurvature u G z')) := by
    rw [hessianOperator_comp hu.contDiffAt (hG.of_le (by norm_num)).contDiffAt,
      hessianOperator_comp hu.contDiffAt (hG.of_le (by norm_num)).contDiffAt]
    change (A - B) - hessianCongruence Q
      ((hessianCongruence J A + chartCurvature u G z) -
        (hessianCongruence K B + chartCurvature u G z')) = _
    simp only [hessianCongruence_sub, hessianCongruence_add,
      hessianCongruence_inverse Q J A hJQ, hessianCongruence_inverse Q J B hJQ]
    abel
  change ‖(A - B) - _‖ ≤ _
  rw [hid]
  have hDG : ContDiff ℝ 2 (fderiv ℝ G) := hG.fderiv_right (by norm_num)
  have hJK : ‖J - K‖ ≤ V * ‖z - z'‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le (fun y (_ : y ∈ S) => hDG.differentiable (by norm_num) y)
      (fun y hy => (second_fderiv_norm_le_iterated y).trans (hG2 y hy)) hS hz' hz
  have hvar : ‖hessianCongruence K B - hessianCongruence J B‖ ≤ 2 * V ^ 3 * ‖z - z'‖ := by
    rw [norm_sub_rev]
    apply (hessianCongruence_variation J K B).trans
    have h1 := mul_le_mul (mul_le_mul hJK (hu2 z' hz') (norm_nonneg _) (by positivity))
      (hG1 z hz) (norm_nonneg _) (by positivity)
    have h2 := mul_le_mul (mul_le_mul (hG1 z' hz') (hu2 z' hz') (norm_nonneg _) hV)
      hJK (norm_nonneg _) (by positivity)
    dsimp [J, K, B] at *
    nlinarith
  have hcur := chartCurvature_lipschitz hu hG hS hV hu1 hu2 hG1 hG2 hG3 hz hz'
  have hinner := (norm_sub_le _ _).trans (add_le_add hvar hcur)
  apply (hessianCongruence_norm Q _).trans
  have hq2 : ‖Q‖ ^ 2 ≤ V ^ 2 := by nlinarith [norm_nonneg Q]
  have hh := mul_le_mul hq2 hinner (norm_nonneg _) (sq_nonneg V)
  nlinarith

end OAI.Analysis.PDE.Elliptic
