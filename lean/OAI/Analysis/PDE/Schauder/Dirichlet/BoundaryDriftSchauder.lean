import OAI.Analysis.PDE.Schauder.Calculus.Schauder.AffineBounds
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.FrozenOperator
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.ScaledEquiv
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.JetTransform
import OAI.Analysis.PDE.Schauder.Dirichlet.RadialDriftSchauder
import OAI.Analysis.PDE.Schauder.Dirichlet.AffineDrift

/-! Uniform flat-boundary estimates including a Hölder drift. The drift
is transported by the actual affine normalization and absorbed by lower-jet
interpolation. Constants are uniform over bounded coefficient families. -/

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem uniform_boundary_local_schauder_with_drift {m : ℕ} (hm : 3 ≤ m) (k : Fin m)
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
        ∀ x ∈ ball x₀ δ, 0 ≤ x k → ∀ y ∈ ball x₀ δ, 0 ≤ y k →
          ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
            (ε * H + D * (‖F‖ + M)) * ‖x-y‖^α := by
  let E := EuclideanSpace ℝ (Fin m)
  obtain ⟨P, hP, hlocal⟩ := halfspace_radial_schauder_with_drift hm k hα hα1
  let ρ' := min 1 (ρ / (Real.sqrt Λ + 1))
  have hρ' : 0 < ρ' := lt_min zero_lt_one (div_pos hρ (by positivity))
  obtain ⟨r, hr, hrρ, hfrozen⟩ := exists_uniform_boundary_frozen_data
    hα hα1 hell hΛ hN hP.le hρ'
  have hrone : r ≤ 1 := (hrρ.trans_le (min_le_left _ _)).le
  have hrnear : r < ρ / (Real.sqrt Λ + 1) := hrρ.trans_le (min_le_right _ _)
  let J := r⁻¹ * (Real.sqrt ell)⁻¹
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  let K := J^2 * J^α
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let δ := (1/8) / (J + 1)
  have hδ : 0 < δ := div_pos (by norm_num) (by positivity)
  let I : OAI.Analysis.Normed.Function.Holder.HolderMap E (Matrix (Fin m) (Fin m) ℝ) α := OAI.Analysis.Normed.Function.Holder.HolderMap.constant 1
  let Q := 1 + (Real.sqrt Λ)^α
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  let Nb' := r^2 * J * Q * Nb
  have hNb' : 0 ≤ Nb' := by dsimp only [Nb']; positivity
  refine ⟨r, hr, hrone, hrnear, δ, hδ, ?_⟩
  intro ε hε
  let ε' := ε / (K + 1)
  have hε' : 0 < ε' := div_pos hε (by positivity)
  obtain ⟨D₀, hD₀, hestimate⟩ := hlocal (‖I‖ + 1) Nb' ε' (by positivity) hNb' hε'
  let D := (K + 1) * D₀ * (Q + 1)
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro A hAn x₀ hx₀ hA hlower hupper
  obtain ⟨d⟩ := hfrozen A hAn x₀ k hA hlower hupper
  refine ⟨d.L, ⟨d.c, d.c_pos, d.normal⟩, d.norm_L, d.norm_inv, ?_⟩
  intro b hbn u hu hz F H M hH hM hbound heq hh
  let T := scaledLinearEquiv d.L hr.ne'
  let v := fun x : E => u (x₀ + d.L (r • x))
  have hT (x : E) : T x = d.L (r • x) := scaledLinearEquiv_apply _ _ x
  have hTnorm : ‖T.toContinuousLinearMap‖ ≤ Real.sqrt Λ :=
    (norm_scaledLinearEquiv_le d.L hr d.norm_L).trans (by nlinarith [Real.sqrt_nonneg Λ])
  have hTinv : ‖T.symm.toContinuousLinearMap‖ ≤ J := norm_scaledLinearEquiv_inv_le d.L hr d.norm_inv
  have hv : ContDiff ℝ 3 v := hu.comp (contDiff_const.add (d.L.contDiff.comp (contDiff_id.const_smul r)))
  have hcoord (x : E) : (x₀ + d.L (r • x)) k = (r*d.c)*x k :=
    scaled_boundary_affine_coordinate k d.L x₀ hx₀ d.normal x
  have hnear (x : E) (hx : ‖x‖ ≤ 1) : x₀ + d.L (r • x) ∈ ball x₀ ρ :=
    scaled_boundary_affine_mem_ball d.L x₀ hr (Real.sqrt_nonneg Λ) d.norm_L hrnear x hx
  let F' := (r^2) • holderLinearAffinePullback hα.le F x₀ T.toContinuousLinearMap
  have hFval (x : E) : OAI.Analysis.Normed.Function.Holder.HolderMap.value F' x = r^2 * OAI.Analysis.Normed.Function.Holder.HolderMap.value F (x₀ + d.L (r • x)) := by
    change r^2 * OAI.Analysis.Normed.Function.Holder.HolderMap.value F (x₀ + T x) = _
    rw [hT]
  have hFn : ‖F'‖ ≤ Q * ‖F‖ :=
    norm_scaled_affine_forcing_le hα.le hr.le hrone (Real.sqrt_nonneg Λ)
      F x₀ T.toContinuousLinearMap hTnorm
  let b' := affineDriftHolder hα.le b x₀ T (r^2)
  have hbn' : ‖b'‖ ≤ Nb' :=
    norm_scaled_affine_drift_le hα.le (Real.sqrt_nonneg Λ) hJ hNb
      b hbn x₀ T hTnorm hTinv
  have hb := hestimate d.B d.small_B
    ((norm_sub_le I d.B).trans (by linarith [d.norm_B])) b' hbn'
    v hv (by
      intro x hxR hx
      exact hz _ (hnear x hxR) (by rw [hcoord, hx, mul_zero]))
    F' H M hH hM (by
      intro x hxR hxk
      exact hbound _ (hnear x hxR) (by rw [hcoord]; exact mul_nonneg (mul_nonneg hr.le d.c_pos.le) hxk)) hh (by
      intro x hxR hx
      have hbval := affineDriftHolder_derivative hα.le b u (hu.differentiable (by norm_num)) x₀ T (r^2) x
      have hbval' : fderiv ℝ v x (OAI.Analysis.Normed.Function.Holder.HolderMap.value b' x) =
          r^2 * fderiv ℝ u (x₀ + d.L (r • x)) (OAI.Analysis.Normed.Function.Holder.HolderMap.value b (x₀ + d.L (r • x))) := by
        simpa only [v, b', hT] using hbval
      rw [d.equation u (hu.of_le (by norm_num)) x hxR, hFval, hbval',
        heq _ (hnear x hxR) (by rw [hcoord]; exact mul_nonneg (mul_nonneg hr.le d.c_pos.le) hx)]
      ring)
  have hsmall : ∀ x ∈ ball 0 (1/8), 0 ≤ x k → ∀ y ∈ ball 0 (1/8), 0 ≤ y k →
      ‖fderiv ℝ (fderiv ℝ (fun z => u (x₀ + T z))) x - fderiv ℝ (fderiv ℝ (fun z => u (x₀ + T z))) y‖ ≤
        (ε' * H + D₀ * (‖F'‖ + M)) * ‖x-y‖^α := by
    simpa only [v, hT] using hb
  have hback := halfspace_hessian_holder_of_affine k u (hu.of_le (by norm_num)) T x₀ hx₀
    (show (0 : ℝ) < 1/8 by norm_num) hα.le (by positivity : 0 ≤ ε' * H + D₀ * (‖F'‖ + M))
    hJ hTinv (mul_pos hr d.c_pos) (by
      intro x
      rw [hT, d.normal]
      change d.c * (r * x k) = (r * d.c) * x k
      ring) hsmall
  intro x hx hxk y hy hyk
  apply (hback x hx hxk y hy hyk).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
  change K * (ε' * H + D₀ * (‖F'‖ + M)) ≤ ε * H + D * (‖F‖ + M)
  exact schauder_pullback_constant_bound hK hQ.le hD₀.le hε.le hH hM
    (norm_nonneg F) hFn


end OAI.Analysis.PDE.Schauder
