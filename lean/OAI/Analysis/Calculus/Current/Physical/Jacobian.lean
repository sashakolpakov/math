import OAI.Analysis.Calculus.Current.Physical.Inverse

/-! The real Jacobian of the inverse physical fiber coordinates. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open scoped Topology

theorem contDiffAt_physicalFiberCoordinates {d : ℕ} (a : ℝ) (τ : ℂ)
    (q : Option (Fin d) → ℂ) (hY : physicalEmbedding τ q none ≠ 0) :
    ContDiffAt ℂ 2 (physicalFiberCoordinates a τ) q := by
  apply contDiffAt_pi.mpr
  intro b
  cases b with
  | none =>
    have he : (fun p : Option (Fin d) → ℂ => fiberMap 1 10 (physicalEmbedding τ p) none) =
        (fun p => phi (physicalEmbedding τ p)) := by funext p; simp [fiberMap]
    have hh := (contDiffAt_fiberMap_complex 1 10 (physicalEmbedding τ q) hY none).comp q
      (contDiff_physicalEmbedding_complex τ).contDiffAt
    dsimp only [Function.comp_def] at hh
    rw [he] at hh
    exact hh.div_const a
  | some i =>
    have he : (fun p : Option (Fin d) → ℂ => fiberMap 1 10 (physicalEmbedding τ p) (some i)) =
        (fun p => ratio (physicalEmbedding τ p) i) := by funext p; simp [fiberMap]
    have hh := (contDiffAt_fiberMap_complex 1 10 (physicalEmbedding τ q) hY (some i)).comp q
      (contDiff_physicalEmbedding_complex τ).contDiffAt
    dsimp only [Function.comp_def] at hh
    rw [he] at hh
    exact hh

def physicalInverseJacobian {d : ℕ} (a : ℝ) (τ : ℂ) (u : Option (Fin d) → ℂ) : ℝ :=
  (fderiv ℝ (physicalFiberInverse a τ) u).det

theorem physicalInverseJacobian_ne_zero {d : ℕ} (a : ℝ) (τ : ℂ)
    (u : Option (Fin d) → ℂ) (ha : a ≠ 0)
    (hN : Real.sqrt 2 • τ + a • u none ≠ 0)
    (hD : fiberDenominator (fun i => u (some i)) ≠ 0) :
    physicalInverseJacobian a τ u ≠ 0 := by
  have hY : physicalEmbedding τ (physicalFiberInverse a τ u) none ≠ 0 := by
    rw [physicalEmbedding_inverse]
    exact fiberInverse_Y_ne_zero _ _ _ hN hD
  have hf := ((contDiffAt_physicalFiberCoordinates a τ _ hY).restrict_scalars ℝ).differentiableAt (by norm_num)
  have hg := ((contDiffAt_physicalFiberInverse a τ u hD).restrict_scalars ℝ).differentiableAt (by norm_num)
  have hNcont : ContinuousAt (fun v : Option (Fin d) → ℂ => Real.sqrt 2 • τ + a • v none) u :=
    continuousAt_const.add ((continuous_apply none).continuousAt.const_smul a)
  have hDcont : ContinuousAt (fun v : Option (Fin d) → ℂ => fiberDenominator (fun i => v (some i))) u := by
    unfold fiberDenominator fiberQuadratic
    fun_prop
  have heq : (physicalFiberCoordinates a τ ∘ physicalFiberInverse a τ) =ᶠ[𝓝 u] id := by
    filter_upwards [hNcont.eventually_ne hN, hDcont.eventually_ne hD] with v hvN hvD
    exact physicalCoordinates_right_inverse a τ v ha hvN hvD
  have hchain := hf.hasFDerivAt.comp u hg.hasFDerivAt
  have hd := heq.fderiv_eq (𝕜 := ℝ)
  rw [hchain.fderiv, fderiv_id] at hd
  have hdet := congrArg (fun L : (Option (Fin d) → ℂ) →L[ℝ] (Option (Fin d) → ℂ) => L.det) hd
  change (LinearMap.comp
      (fderiv ℝ (physicalFiberCoordinates a τ) (physicalFiberInverse a τ u)).toLinearMap
      (fderiv ℝ (physicalFiberInverse a τ) u).toLinearMap).det = (LinearMap.id).det at hdet
  rw [LinearMap.det_comp, LinearMap.det_id] at hdet
  intro hz
  change (fderiv ℝ (physicalFiberInverse a τ) u).toLinearMap.det = 0 at hz
  rw [hz, mul_zero] at hdet
  exact zero_ne_one hdet

theorem physicalFiberInverse_fderiv_scale {d : ℕ} (a : ℝ) (τ : ℂ)
    (u : Option (Fin d) → ℂ) (hD : fiberDenominator (fun i => u (some i)) ≠ 0) :
    fderiv ℝ (physicalFiberInverse a (a • τ)) u = a • fderiv ℝ (physicalFiberInverse 1 τ) u := by
  have hg := ((contDiffAt_physicalFiberInverse 1 τ u hD).restrict_scalars ℝ).differentiableAt (by norm_num)
  have hh : HasFDerivAt (physicalFiberInverse a (a • τ))
      (a • fderiv ℝ (physicalFiberInverse 1 τ) u) u := by
    have he : physicalFiberInverse (d := d) a (a • τ) = a • physicalFiberInverse 1 τ :=
      funext (physicalFiberInverse_scale a τ)
    rw [he]
    exact hg.hasFDerivAt.const_smul a
  exact hh.fderiv

theorem physicalInverseJacobian_scale {d : ℕ} (a : ℝ) (τ : ℂ)
    (u : Option (Fin d) → ℂ) (hD : fiberDenominator (fun i => u (some i)) ≠ 0) :
    physicalInverseJacobian a (a • τ) u = a ^ (2 * (d + 1)) * physicalInverseJacobian 1 τ u := by
  unfold physicalInverseJacobian
  rw [physicalFiberInverse_fderiv_scale a τ u hD]
  change LinearMap.det (a • (fderiv ℝ (physicalFiberInverse 1 τ) u).toLinearMap) = _
  rw [LinearMap.det_smul]
  congr 2
  simp [Module.finrank_pi_fintype, Nat.mul_comm]

end OAI.Analysis.Calculus.Current
