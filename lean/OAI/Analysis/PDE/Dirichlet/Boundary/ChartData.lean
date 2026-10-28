import OAI.Analysis.PDE.Elliptic.DirichletChartEllipticity
import OAI.Analysis.PDE.Elliptic.Boundary.HalfPatch
import OAI.Analysis.PDE.Dirichlet.Periodic.Chart.SchauderReturnBounds

open Set Metric InnerProductSpace
open scoped Topology Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Elliptic OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

theorem coordinate_half_patch_diameter (k : Fin m) :
    ∀ x ∈ OAI.Analysis.PDE.Elliptic.closedCoordinateHalfPatch k (0 : E) (1/2),
      ∀ y ∈ OAI.Analysis.PDE.Elliptic.closedCoordinateHalfPatch k (0 : E) (1/2), ‖x-y‖ ≤ 1 := by
  intro x hx y hy
  have hx' : ‖x‖ ≤ (1/2 : ℝ) := by simpa only [mem_closedBall, dist_zero_right] using hx.1
  have hy' : ‖y‖ ≤ (1/2 : ℝ) := by simpa only [mem_closedBall, dist_zero_right] using hy.1
  exact (norm_sub_le x y).trans (by linarith)

theorem chart_matrix_ellipticity (J D A : E →L[ℝ] E)
    (hinv : J.comp D = ContinuousLinearMap.id ℝ E)
    (hA : A.toLinearMap.IsSymmetric) {C ell Λ : ℝ}
    (hC : 0 < C) (hJ : ‖J‖ ≤ C) (hD : ‖D‖ ≤ C)
    (hell : 0 < ell) (hΛ : 0 ≤ Λ)
    (hlo : ∀ v : E, ell * ‖v‖^2 ≤ inner ℝ v (A v))
    (hhi : ∀ v : E, inner ℝ v (A v) ≤ Λ * ‖v‖^2) :
    (OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrix (OAI.Analysis.PDE.Elliptic.pullbackEllipticOperator J A)).PosDef ∧
      (∀ v : E, (ell / C^2) * ‖v‖^2 ≤ inner ℝ v
        (Matrix.toEuclideanCLM (𝕜 := ℝ)
          (OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrix (OAI.Analysis.PDE.Elliptic.pullbackEllipticOperator J A)) v)) ∧
      (∀ v : E, inner ℝ v
        (Matrix.toEuclideanCLM (𝕜 := ℝ)
          (OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrix (OAI.Analysis.PDE.Elliptic.pullbackEllipticOperator J A)) v) ≤
          (Λ * C^2) * ‖v‖^2) := by
  have hs := OAI.Analysis.PDE.Schauder.pullback_coefficient_isSymmetric J A hA
  have hb := OAI.Analysis.PDE.Elliptic.pullbackEllipticOperator_uniform_bounds J D A hinv hC hJ hD hell.le hΛ hlo hhi
  have hp : (OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrix (OAI.Analysis.PDE.Elliptic.pullbackEllipticOperator J A)).PosDef := by
    apply OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrix_posDef _ hs
    intro v hv
    rw [real_inner_comm]
    exact (mul_pos (div_pos hell (sq_pos_of_pos hC))
      (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le (hb v).1
  refine ⟨hp, ?_, ?_⟩
  · intro v
    rw [OAI.Analysis.PDE.Schauder.toEuclideanCLM_euclideanCoefficientMatrix _ hs]
    exact (hb v).1
  · intro v
    rw [OAI.Analysis.PDE.Schauder.toEuclideanCLM_euclideanCoefficientMatrix _ hs]
    exact (hb v).2

theorem SchauderJetBoundsOn.mono_bound {u : E → ℝ} {S : Set E} {α M N : ℝ}
    (h : SchauderJetBoundsOn u S α M) (hMN : M ≤ N) :
    SchauderJetBoundsOn u S α N := by
  refine ⟨fun x hx => (h.value x hx).trans hMN,
    fun x hx => (h.first x hx).trans hMN,
    fun x hx => (h.second x hx).trans hMN, ?_⟩
  intro x hx y hy
  exact (h.second_holder x hx y hy).trans
    (mul_le_mul_of_nonneg_right hMN (Real.rpow_nonneg (norm_nonneg _) _))

theorem SchauderJetBoundsOn.mono_set {u : E → ℝ} {S T : Set E} {α M : ℝ}
    (h : SchauderJetBoundsOn u S α M) (hTS : T ⊆ S) :
    SchauderJetBoundsOn u T α M :=
  ⟨fun x hx => h.value x (hTS hx), fun x hx => h.first x (hTS hx),
    fun x hx => h.second x (hTS hx),
    fun x hx y hy => h.second_holder x (hTS hx) y (hTS hy)⟩

end OAI.Analysis.PDE.Dirichlet
