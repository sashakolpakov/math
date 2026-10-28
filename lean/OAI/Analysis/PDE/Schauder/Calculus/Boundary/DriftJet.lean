import OAI.Analysis.PDE.Schauder.Dirichlet.BoundaryDriftSchauder
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.LocalBounds

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem uniform_boundary_local_jet_schauder_with_drift {m : ℕ} (hm : 3 ≤ m) (k : Fin m)
    {α ell Λ N Nb ρ : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hell : 0 < ell) (hΛ : 0 ≤ Λ) (hN : 0 ≤ N) (hNb : 0 ≤ Nb) (hρ : 0 < ρ) :
    ∃ (r : ℝ), r > 0 ∧ r ≤ 1 ∧ r < ρ / (Real.sqrt Λ + 1) ∧ ∃ δ > 0, ∀ ε > 0, ∃ D > 0,
      ∀ A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α,
      ‖A‖ ≤ N → ∀ x₀ : EuclideanSpace ℝ (Fin m), x₀ k = 0 →
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x₀).PosDef →
      (∀ x : EuclideanSpace ℝ (Fin m), ell * ‖x‖^2 ≤
        inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x₀) x)) →
      (∀ x : EuclideanSpace ℝ (Fin m),
        inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x₀) x) ≤ Λ * ‖x‖^2) →
      ∃ L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
        (∃ c > 0, ∀ z, L z k = c * z k) ∧
        ‖L.toContinuousLinearMap‖ ≤ Real.sqrt Λ ∧
        ‖L.symm.toContinuousLinearMap‖ ≤ (Real.sqrt ell)⁻¹ ∧
        ∀ b : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m)) α,
        ‖b‖ ≤ Nb →
        ∀ (u : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 3 u →
        (∀ x ∈ ball x₀ ρ, x k = 0 → u x = 0) →
        ∀ (F : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α) H M, 0 ≤ H → 0 ≤ M →
        (∀ x ∈ ball x₀ ρ, 0 ≤ x k → |u x| ≤ M) →
        (∀ x ∈ ball x₀ ρ, 0 ≤ x k → nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) u x =
          OAI.Analysis.Normed.Function.Holder.HolderMap.value F x + fderiv ℝ u x (OAI.Analysis.Normed.Function.Holder.HolderMap.value b x)) →
        (∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
          ‖fderiv ℝ (fderiv ℝ (fun z => radialCutoff (1/2) z * u (x₀ + L (r • z)))) x -
            fderiv ℝ (fderiv ℝ (fun z => radialCutoff (1/2) z * u (x₀ + L (r • z)))) y‖ ≤ H * ‖x-y‖^α) →
        (∀ x ∈ ball x₀ δ, 0 ≤ x k →
          |u x| ≤ M ∧ ‖fderiv ℝ u x‖ ≤ ε*H+D*(‖F‖+M) ∧
            ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ ε*H+D*(‖F‖+M)) ∧
        ∀ x ∈ ball x₀ δ, 0 ≤ x k → ∀ y ∈ ball x₀ δ, 0 ≤ y k →
          ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
            (ε * H + D * (‖F‖ + M)) * ‖x-y‖^α := by
  let E := EuclideanSpace ℝ (Fin m)
  obtain ⟨r, hr, hrone, hrnear, δ, hδ, hlocal⟩ :=
    uniform_boundary_local_schauder_with_drift hm k hα hα1 hell hΛ hN hNb hρ
  let J := r⁻¹ * (Real.sqrt ell)⁻¹
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  let δ' := min δ ((1/4)/(J+1))
  have hδ' : 0 < δ' := lt_min hδ (div_pos (by norm_num) (by positivity))
  refine ⟨r, hr, hrone, hrnear, δ', hδ', ?_⟩
  intro ε hε
  obtain ⟨D₀, hD₀, hestimate⟩ := hlocal ε hε
  obtain ⟨D₁, hD₁, hlowerjet⟩ := affine_halfspace_local_lower_jets k hα hα1.le hJ hε
  let D := D₀ + D₁ + 1
  have hD : 0 < D := by dsimp only [D]; positivity
  have hD₀D : D₀ ≤ D := by dsimp only [D]; linarith
  have hD₁D : D₁ ≤ D := by dsimp only [D]; linarith
  refine ⟨D, hD, ?_⟩
  intro A hAn x₀ hx₀ hA hlower hupper
  obtain ⟨L, ⟨c, hc, hnormal⟩, hL, hLi, hLestimate⟩ :=
    hestimate A hAn x₀ hx₀ hA hlower hupper
  refine ⟨L, ⟨c, hc, hnormal⟩, hL, hLi, ?_⟩
  intro b hbn u hu hz F H M hH hM hbound heq hh
  have hhess := hLestimate b hbn u hu hz F H M hH hM hbound heq hh
  let T := scaledLinearEquiv L hr.ne'
  have hT (x : E) : T x = L (r • x) := scaledLinearEquiv_apply _ _ x
  have hTi : ‖T.symm.toContinuousLinearMap‖ ≤ J := norm_scaledLinearEquiv_inv_le L hr hLi
  have hTnormal (x : E) : T x k = (r*c)*x k := by
    rw [hT, hnormal]
    change c*(r*x k) = (r*c)*x k
    ring
  have hcoord (x : E) : (x₀ + T x) k = (r*c)*x k := by
    simp only [PiLp.add_apply, hx₀, zero_add, hTnormal]
  have hnear (x : E) (hx : ‖x‖ ≤ 1) : x₀ + T x ∈ ball x₀ ρ := by
    rw [hT]
    exact scaled_boundary_affine_mem_ball L x₀ hr (Real.sqrt_nonneg Λ) hL hrnear x hx
  have houterbound : ∀ z, 0 ≤ z k → |radialCutoff (1/2) z * u (x₀ + T z)| ≤ M := by
    intro z hzk
    by_cases hzR : ‖z‖ ≤ 1
    · have hvb := hbound _ (hnear z hzR) (by
        rw [hcoord]
        exact mul_nonneg (mul_nonneg hr.le hc.le) hzk)
      rw [abs_mul, abs_of_nonneg (radialCutoff_nonneg _ _)]
      exact (mul_le_mul_of_nonneg_right (radialCutoff_le_one _ _) (abs_nonneg _)).trans
        (by simpa using hvb)
    · have hz0 : radialCutoff (1/2) z = 0 :=
        radialCutoff_zero (by norm_num) (by linarith [not_le.mp hzR])
      rw [hz0, zero_mul, abs_zero]
      exact hM
  have hjets := hlowerjet T hTi (r*c) (mul_pos hr hc) hTnormal x₀ hx₀
    u (hu.of_le (by norm_num)) H M hH hM houterbound (by simpa only [hT] using hh)
  constructor
  · intro x hx hxk
    have hx' : x ∈ ball x₀ ((1/4)/(J+1)) :=
      (ball_subset_ball (min_le_right _ _)) hx
    obtain ⟨hvalue, hfirst, hsecond⟩ := hjets x hx' hxk
    have hmore : D₁*M ≤ D*(‖F‖+M) :=
      (mul_le_mul_of_nonneg_right hD₁D hM).trans
        (mul_le_mul_of_nonneg_left (by linarith [norm_nonneg F]) hD.le)
    exact ⟨hvalue, hfirst.trans (by linarith), hsecond.trans (by linarith)⟩
  · intro x hx hxk y hy hyk
    have hx' : x ∈ ball x₀ δ := (ball_subset_ball (min_le_left _ _)) hx
    have hy' : y ∈ ball x₀ δ := (ball_subset_ball (min_le_left _ _)) hy
    apply (hhess x hx' hxk y hy' hyk).trans
    gcongr

end OAI.Analysis.PDE.Schauder
