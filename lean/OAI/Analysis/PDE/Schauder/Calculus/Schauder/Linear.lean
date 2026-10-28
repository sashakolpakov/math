import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Compact

/-! Real linear changes of variables for the actual Hessian and the elliptic operator. -/

noncomputable section
open _root_.MeasureTheory Set Metric InnerProductSpace Laplacian
namespace OAI.Analysis.PDE.Schauder

theorem second_fderiv_comp_linear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℝ) (hu : ContDiff ℝ 2 u) (L : E →L[ℝ] E) (x v w : E) :
    fderiv ℝ (fderiv ℝ (u ∘ L)) x v w = fderiv ℝ (fderiv ℝ u) (L x) (L v) (L w) := by
  have hD : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hDcomp : ContDiff ℝ 1 (fderiv ℝ (u ∘ L)) := (hu.comp L.contDiff).fderiv_right (by norm_num)
  have he : (fun y => fderiv ℝ (u ∘ L) y w) = fun y => fderiv ℝ u (L y) (L w) := by
    funext y
    rw [fderiv_comp y (hu.differentiable (by norm_num) _) L.differentiableAt, L.fderiv]
    rfl
  rw [← fderiv_apply_const _ x w v (hDcomp.differentiable one_ne_zero x), he]
  have hfun : (fun y => fderiv ℝ u (L y) (L w)) = (fun y => fderiv ℝ u y (L w)) ∘ L := rfl
  rw [hfun, fderiv_comp x ((hD.clm_apply contDiff_const).differentiable one_ne_zero _) L.differentiableAt,
    L.fderiv, ContinuousLinearMap.comp_apply,
    fderiv_apply_const _ (L x) (L w) (L v) (hD.differentiable one_ne_zero _)]

theorem bilinear_trace_pullback {m : ℕ}
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (p : Fin m → EuclideanSpace ℝ (Fin m)) :
    (∑ k, B (p k) (p k)) = ∑ i : Fin m, ∑ j : Fin m,
      (∑ k, p k i * p k j) * B (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) := by
  have he : (∑ k, B (p k) (p k)) = ∑ k : Fin m, ∑ i : Fin m, ∑ j : Fin m,
      (p k i * p k j) * B (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) :=
    Finset.sum_congr rfl (fun k _ => euclidean_bilinear_expansion B (p k) (p k))
  rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_mul]

def linearEllipticMatrix {m : ℕ} (L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    Matrix (Fin m) (Fin m) ℝ := fun i j =>
      ∑ k : Fin m, (L (EuclideanSpace.single k (1 : ℝ))) i * (L (EuclideanSpace.single k (1 : ℝ))) j

theorem laplacian_comp_linear {m : ℕ} (u : EuclideanSpace ℝ (Fin m) → ℝ)
    (hu : ContDiff ℝ 2 u) (L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin m)) :
    laplacian (u ∘ L) x = ∑ i : Fin m, ∑ j : Fin m,
      linearEllipticMatrix L i j * fderiv ℝ (fderiv ℝ u) (L x)
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) := by
  rw [laplacian_coordinate]
  simp_rw [second_fderiv_comp_linear u hu L]
  exact bilinear_trace_pullback _ _

theorem bilinear_norm_le_pullback {m : ℕ}
    (A B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (h : ∀ v w, A v w = B (L v) (L w)) :
    ‖A‖ ≤ ‖B‖ * ‖L‖ ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [h]
  calc
    _ ≤ ‖B (L v)‖ * ‖L w‖ := (B (L v)).le_opNorm _
    _ ≤ (‖B‖ * ‖L v‖) * ‖L w‖ := mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _)
    _ ≤ (‖B‖ * (‖L‖ * ‖v‖)) * (‖L‖ * ‖w‖) := by gcongr <;> exact L.le_opNorm _
    _ = _ := by ring

end OAI.Analysis.PDE.Schauder
