import OAI.Analysis.PDE.Schauder.Calculus.Schauder.AffineBounds
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.FrozenOperator
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.ScaledEquiv
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.JetTransform
import OAI.Analysis.PDE.Schauder.Calculus.Interior.Nested
import OAI.Analysis.PDE.Schauder.Calculus.Interior.Unnormalize
import OAI.Analysis.PDE.Schauder.Calculus.Interior.LocalBounds

/-! A uniform local interior estimate for a bounded elliptic Hölder
family. The arbitrarily small top-order error is measured on a fixed larger
normalized cutoff; all remaining terms use only the forcing and the value. -/

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem uniform_interior_local_jet_schauder {m : ℕ} (hm : 3 ≤ m) (k : Fin m)
    {α ell Λ N ρ : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hell : 0 < ell) (hΛ : 0 ≤ Λ) (hN : 0 ≤ N) (hρ : 0 < ρ) :
    ∃ (r : ℝ), r > 0 ∧ r ≤ 1 ∧ r < ρ / (Real.sqrt Λ + 1) ∧
      r < ρ / (2 * Real.sqrt Λ + 1) ∧ ∃ δ > 0, ∀ ε > 0, ∃ D > 0,
      ∀ A : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α,
      ‖A‖ ≤ N → ∀ x₀ : EuclideanSpace ℝ (Fin m),
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x₀).PosDef →
      (∀ x : EuclideanSpace ℝ (Fin m), ell * ‖x‖^2 ≤
        inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x₀) x)) →
      (∀ x : EuclideanSpace ℝ (Fin m),
        inner ℝ x (Matrix.toEuclideanCLM (𝕜 := ℝ) (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x₀) x) ≤ Λ * ‖x‖^2) →
      ∃ L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
        ‖L.toContinuousLinearMap‖ ≤ Real.sqrt Λ ∧
        ‖L.symm.toContinuousLinearMap‖ ≤ (Real.sqrt ell)⁻¹ ∧
        ∀ (u : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 3 u →
        ∀ (F : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α) H M, 0 ≤ H → 0 ≤ M →
        (∀ x ∈ ball x₀ ρ, |u x| ≤ M) →
        (∀ x ∈ ball x₀ ρ, nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A) u x = OAI.Analysis.Normed.Function.Holder.HolderMap.value F x) →
        (∀ x, ∀ y,
          ‖fderiv ℝ (fderiv ℝ (fun z => radialCutoff (1/2) z * u (x₀ + L (r • z)))) x -
            fderiv ℝ (fderiv ℝ (fun z => radialCutoff (1/2) z * u (x₀ + L (r • z)))) y‖ ≤ H * ‖x-y‖^α) →
        (∀ x ∈ ball x₀ δ,
          |u x| ≤ M ∧ ‖fderiv ℝ u x‖ ≤ ε*H+D*(‖F‖+M) ∧
            ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ ε*H+D*(‖F‖+M)) ∧
        ∀ x ∈ ball x₀ δ, ∀ y ∈ ball x₀ δ,
          ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
            (ε * H + D * (‖F‖ + M)) * ‖x-y‖^α := by
  let E := EuclideanSpace ℝ (Fin m)
  let χ : E → ℝ := radialCutoff (1/8)
  let η : E → ℝ := radialCutoff (1/2)
  have hχ : ContDiff ℝ 3 χ := (contDiff_radialCutoff _).of_le (by simp)
  have hχc : HasCompactSupport χ := hasCompactSupport_radialCutoff (by norm_num)
  have hχquarter : tsupport χ ⊆ closedBall 0 (1/4) := by
    simpa only [show (2 : ℝ)*(1/8) = 1/4 by norm_num] using
      (tsupport_radialCutoff_subset (E := E) (r := 1/8) (by norm_num))
  have hχR : tsupport χ ⊆ closedBall 0 1 := hχquarter.trans (closedBall_subset_closedBall (by norm_num))
  have hη : ContDiff ℝ 3 η := (contDiff_radialCutoff _).of_le (by simp)
  have hηc : HasCompactSupport η := hasCompactSupport_radialCutoff (by norm_num)
  have hηR : tsupport η ⊆ closedBall 0 1 := by
    simpa only [show (2 : ℝ)*(1/2) = 1 by norm_num] using
      (tsupport_radialCutoff_subset (E := E) (r := 1/2) (by norm_num))
  have hηone (x) (hx : x ∈ tsupport χ) : η =ᶠ[𝓝 x] fun _ => 1 := by
    have hxq : ‖x‖ ≤ 1/4 := by simpa only [mem_closedBall, dist_zero_right] using hχquarter hx
    have hb : ∀ᶠ y in 𝓝 x, y ∈ ball 0 (1/2) := isOpen_ball.mem_nhds (by
      simpa only [mem_ball, dist_zero_right] using (show ‖x‖ < (1/2 : ℝ) by linarith))
    filter_upwards [hb] with y hy
    exact radialCutoff_one (by norm_num) (le_of_lt (by simpa only [mem_ball, dist_zero_right] using hy))
  obtain ⟨P, hP, hlocal⟩ := fullspace_nested_cutoff_schauder hm k hα hα1 (show (0 : ℝ) < 1 by norm_num)
  let ρ' := min 1 (ρ / (2 * Real.sqrt Λ + 1))
  have hρ' : 0 < ρ' := lt_min zero_lt_one (div_pos hρ (by positivity))
  obtain ⟨r, hr, hrρ, hfrozen⟩ := exists_uniform_boundary_frozen_data
    hα hα1 hell hΛ hN hP.le hρ'
  have hrone : r ≤ 1 := (hrρ.trans_le (min_le_left _ _)).le
  have hrnear₂ : r < ρ / (2 * Real.sqrt Λ + 1) := hrρ.trans_le (min_le_right _ _)
  have hrnear : r < ρ / (Real.sqrt Λ + 1) := hrnear₂.trans_le
    (div_le_div_of_nonneg_left hρ.le (by positivity) (by nlinarith [Real.sqrt_nonneg Λ]))
  let J := r⁻¹ * (Real.sqrt ell)⁻¹
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  let K := J^2 * J^α
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let δ := (1/8) / (J + 1)
  have hδ : 0 < δ := div_pos (by norm_num) (by positivity)
  let I : OAI.Analysis.Normed.Function.Holder.HolderMap E (Matrix (Fin m) (Fin m) ℝ) α := OAI.Analysis.Normed.Function.Holder.HolderMap.constant 1
  let Q := 1 + (Real.sqrt Λ)^α
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  refine ⟨r, hr, hrone, hrnear, hrnear₂, δ, hδ, ?_⟩
  intro ε hε
  let ε' := ε / (K + 1)
  have hε' : 0 < ε' := div_pos hε (by positivity)
  obtain ⟨D₀, hD₀, hestimate⟩ := hlocal χ hχ hχc hχR (‖I‖ + 1) ε' (by positivity) hε'
  obtain ⟨D₁, hD₁, hlowerjet⟩ := affine_fullspace_local_lower_jets k hα hα1.le hJ hε
  let D := (K + 1) * D₀ * (Q + 1) + D₁
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro A hAn x₀ hA hlower hupper
  obtain ⟨d⟩ := hfrozen A hAn x₀ k hA hlower hupper
  refine ⟨d.L, d.norm_L, d.norm_inv, ?_⟩
  intro u hu F H M hH hM hbound heq hh
  let T := scaledLinearEquiv d.L hr.ne'
  let v := fun x : E => u (x₀ + d.L (r • x))
  have hT (x : E) : T x = d.L (r • x) := scaledLinearEquiv_apply _ _ x
  have hTnorm : ‖T.toContinuousLinearMap‖ ≤ Real.sqrt Λ :=
    (norm_scaledLinearEquiv_le d.L hr d.norm_L).trans (by nlinarith [Real.sqrt_nonneg Λ])
  have hTinv : ‖T.symm.toContinuousLinearMap‖ ≤ J := norm_scaledLinearEquiv_inv_le d.L hr d.norm_inv
  have hv : ContDiff ℝ 3 v := hu.comp (contDiff_const.add (d.L.contDiff.comp (contDiff_id.const_smul r)))
  have hnear (x : E) (hx : ‖x‖ ≤ 1) : x₀ + d.L (r • x) ∈ ball x₀ ρ :=
    scaled_boundary_affine_mem_ball d.L x₀ hr (Real.sqrt_nonneg Λ) d.norm_L hrnear x hx
  let F' := (r^2) • holderLinearAffinePullback hα.le F x₀ T.toContinuousLinearMap
  have hFval (x : E) : OAI.Analysis.Normed.Function.Holder.HolderMap.value F' x = r^2 * OAI.Analysis.Normed.Function.Holder.HolderMap.value F (x₀ + d.L (r • x)) := by
    change r^2 * OAI.Analysis.Normed.Function.Holder.HolderMap.value F (x₀ + T x) = _
    rw [hT]
  have hFn : ‖F'‖ ≤ Q * ‖F‖ :=
    norm_scaled_affine_forcing_le hα.le hr.le hrone (Real.sqrt_nonneg Λ)
      F x₀ T.toContinuousLinearMap hTnorm
  have hb := hestimate d.B (by simpa only [show (2 : ℝ)*1+1 = 3 by norm_num] using d.small_B)
    ((norm_sub_le I d.B).trans (by linarith [d.norm_B])) η hη hηc hηone
    (fun x => by rw [abs_of_nonneg (radialCutoff_nonneg _ _)]; exact radialCutoff_le_one _ _)
    v hv
    F' H M hH hM (by
      intro x hx
      have hxR : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hηR hx
      exact hbound _ (hnear x hxR)) hh (by
      intro x hn
      have hxR : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hχR (subset_closure hn)
      rw [d.equation u (hu.of_le (by norm_num)) x hxR, hFval,
        heq _ (hnear x hxR)])
  have hsmall : ∀ x ∈ ball 0 (1/8), ∀ y ∈ ball 0 (1/8),
      ‖fderiv ℝ (fderiv ℝ (fun z => u (x₀ + T z))) x - fderiv ℝ (fderiv ℝ (fun z => u (x₀ + T z))) y‖ ≤
        (ε' * H + D₀ * (‖F'‖ + M)) * ‖x-y‖^α := by
    intro x hx y hy
    have hxnorm : ‖x‖ < 1/8 := by simpa only [mem_ball, dist_zero_right] using hx
    have hynorm : ‖y‖ < 1/8 := by simpa only [mem_ball, dist_zero_right] using hy
    have hbxy := hb x y
    rw [hessian_radialCutoff_mul_eq v (by norm_num) x hxnorm,
      hessian_radialCutoff_mul_eq v (by norm_num) y hynorm] at hbxy
    simpa only [v, hT] using hbxy
  have hback := fullspace_hessian_holder_of_affine u (hu.of_le (by norm_num)) T x₀
    (show (0 : ℝ) < 1/8 by norm_num) hα.le (by positivity : 0 ≤ ε' * H + D₀ * (‖F'‖ + M))
    hJ hTinv hsmall
  have houterbound : ∀ z, |radialCutoff (1/2) z * u (x₀ + T z)| ≤ M := by
    intro z
    by_cases hz : z ∈ tsupport η
    · have hzR : ‖z‖ ≤ 1 := by
        simpa only [mem_closedBall, dist_zero_right] using hηR hz
      have hvb := hbound _ (hnear z hzR)
      rw [hT, abs_mul, abs_of_nonneg (radialCutoff_nonneg _ _)]
      exact (mul_le_mul_of_nonneg_right (radialCutoff_le_one _ _) (abs_nonneg _)).trans
        (by simpa using hvb)
    · have hz0 : radialCutoff (1/2) z = 0 := by
        exact image_eq_zero_of_notMem_tsupport hz
      rw [hz0, zero_mul, abs_zero]
      exact hM
  have hjets := hlowerjet T hTinv x₀ u (hu.of_le (by norm_num)) H M hH hM houterbound
    (by simpa only [hT] using hh)
  constructor
  · intro x hx
    have hx' : x ∈ ball x₀ ((1/4)/(J+1)) := by
      apply (ball_subset_ball ?_) hx
      dsimp only [δ]
      gcongr
      norm_num
    obtain ⟨hvalue, hfirst, hsecond⟩ := hjets x hx'
    have hmore : D₁ * M ≤ D * (‖F‖ + M) := by
      have hDlower : D₁ ≤ D := by
        have hbase : 0 ≤ (K + 1) * D₀ * (Q + 1) := by positivity
        dsimp only [D]
        linarith
      exact (mul_le_mul_of_nonneg_right hDlower hM).trans
        (mul_le_mul_of_nonneg_left (by linarith [norm_nonneg F]) hD.le)
    exact ⟨hvalue, hfirst.trans (by linarith), hsecond.trans (by linarith)⟩
  intro x hx y hy
  apply (hback x hx y hy).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
  change K * (ε' * H + D₀ * (‖F'‖ + M)) ≤ ε * H + D * (‖F‖ + M)
  apply (schauder_pullback_constant_bound hK hQ.le hD₀.le hε.le hH hM
    (norm_nonneg F) hFn).trans
  dsimp only [D]
  nlinarith [norm_nonneg F]


end OAI.Analysis.PDE.Schauder
