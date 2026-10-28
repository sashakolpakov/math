import OAI.Analysis.Calculus.Current.Physical.Compact
import OAI.Analysis.Calculus.Current.Physical.Hessian

/-! The explicit biholomorphic inverse in physical fixed-time coordinates. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

def physicalFiberCoordinates {d : ℕ} (a : ℝ) (τ : ℂ) (q : Option (Fin d) → ℂ) :
    Option (Fin d) → ℂ
  | none => phi (physicalEmbedding τ q) / a
  | some i => ratio (physicalEmbedding τ q) i

def inverseHeight {d : ℕ} (a : ℝ) (τ : ℂ) (u : Option (Fin d) → ℂ) : ℂ :=
  (Real.sqrt 2 • τ + a • u none) / fiberDenominator (fun i => u (some i))

def physicalFiberInverse {d : ℕ} (a : ℝ) (τ : ℂ) (u : Option (Fin d) → ℂ) :
    Option (Fin d) → ℂ
  | none => Real.sqrt 2 • inverseHeight a τ u - τ
  | some i => u (some i) * inverseHeight a τ u

theorem physicalEmbedding_inverse {d : ℕ} (a : ℝ) (τ : ℂ) (u : Option (Fin d) → ℂ) :
    physicalEmbedding τ (physicalFiberInverse a τ u) =
      fiberInverse (Real.sqrt 2 • τ) (fun i => u (some i)) (a • u none) := by
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  funext b
  cases b with
  | none =>
    simp [physicalEmbedding, physicalLift, physicalTimeOffset, physicalFiberInverse,
      inverseHeight, fiberInverse, Complex.real_smul, mul_sub, hs0]
  | some b =>
    cases b with
    | none =>
      simp only [physicalEmbedding, physicalLift, physicalTimeOffset, physicalFiberInverse,
        inverseHeight, fiberInverse, Pi.add_apply, ContinuousLinearMap.pi_apply,
        smul_apply, ContinuousLinearMap.proj_apply, Complex.real_smul,
        Complex.ofReal_inv, Complex.ofReal_neg]
      field_simp
      linear_combination τ * hs
    | some i => simp [physicalEmbedding, physicalLift, physicalTimeOffset, physicalFiberInverse,
        inverseHeight, fiberInverse]

theorem physicalCoordinates_right_inverse {d : ℕ} (a : ℝ) (τ : ℂ)
    (u : Option (Fin d) → ℂ) (ha : a ≠ 0)
    (hN : Real.sqrt 2 • τ + a • u none ≠ 0)
    (hD : fiberDenominator (fun i => u (some i)) ≠ 0) :
    physicalFiberCoordinates a τ (physicalFiberInverse a τ u) = u := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  funext b
  cases b with
  | none =>
    simp only [physicalFiberCoordinates, physicalEmbedding_inverse]
    rw [phi_fiberInverse (Real.sqrt 2 • τ) (a • u none) (fun i => u (some i)) hN hD]
    simp only [Complex.real_smul]
    exact mul_div_cancel_left₀ _ ha'
  | some i =>
    simp only [physicalFiberCoordinates, physicalEmbedding_inverse,
      ratio_fiberInverse _ _ _ hN hD]

theorem physicalCoordinates_left_inverse {d : ℕ} (a : ℝ) (τ : ℂ)
    (q : Option (Fin d) → ℂ) (ha : a ≠ 0)
    (hY : physicalEmbedding τ q none ≠ 0)
    (hD : fiberDenominator (ratio (physicalEmbedding τ q)) ≠ 0) :
    physicalFiberInverse a τ (physicalFiberCoordinates a τ q) = q := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  let z := physicalEmbedding τ q
  have hYz : z none ≠ 0 := hY
  have ht : Real.sqrt 2 • τ = z none - z (some none) := by
    have h := imaginaryTime_physicalEmbedding τ q
    have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    change (z none - z (some none)) / (Real.sqrt 2 : ℂ) = τ at h
    rw [div_eq_iff hs] at h
    simpa only [Complex.real_smul, mul_comm] using h.symm
  have hH : inverseHeight a τ (physicalFiberCoordinates a τ q) = z none := by
    simp only [inverseHeight, physicalFiberCoordinates, Complex.real_smul, mul_div_cancel₀ _ ha']
    change (Real.sqrt 2 * τ + phi z) / fiberDenominator (ratio z) = z none
    rw [show (Real.sqrt 2 : ℂ) * τ = z none - z (some none) from ht,
      ← fiberDenominator_mul_height z]
    exact mul_div_cancel_left₀ _ hD
  funext b
  cases b with
  | none =>
    simp only [physicalFiberInverse, hH]
    exact physicalEmbedding_first τ q
  | some i =>
    simp only [physicalFiberInverse, physicalFiberCoordinates, hH]
    change ratio z i * z none = q (some i)
    rw [show ratio z i * z none = z (some (some i)) by simp [ratio, hYz]]
    simp [z, physicalEmbedding, physicalLift, physicalTimeOffset]

theorem contDiffAt_physicalFiberInverse {d : ℕ} (a : ℝ) (τ : ℂ)
    (u : Option (Fin d) → ℂ) (hD : fiberDenominator (fun i => u (some i)) ≠ 0) :
    ContDiffAt ℂ ⊤ (physicalFiberInverse a τ) u := by
  have hH : ContDiffAt ℂ ⊤ (inverseHeight a τ) u := by
    unfold inverseHeight fiberDenominator fiberQuadratic
    simp only [Complex.real_smul]
    fun_prop (disch := exact hD)
  apply contDiffAt_pi.mpr
  intro b
  cases b with
  | none =>
    change ContDiffAt ℂ ⊤ (fun v => Real.sqrt 2 • inverseHeight a τ v - τ) u
    exact (hH.const_smul (Real.sqrt 2)).sub contDiffAt_const
  | some i =>
    change ContDiffAt ℂ ⊤ (fun v => v (some i) * inverseHeight a τ v) u
    exact (by fun_prop : ContDiffAt ℂ ⊤ (fun v : Option (Fin d) → ℂ => v (some i)) u).mul hH

theorem physicalFiberInverse_scale {d : ℕ} (a : ℝ) (τ : ℂ) (u : Option (Fin d) → ℂ) :
    physicalFiberInverse a (a • τ) u = a • physicalFiberInverse 1 τ u := by
  funext b
  cases b with
  | none =>
    simp only [physicalFiberInverse, inverseHeight, Pi.smul_apply, Complex.real_smul, one_smul]
    ring
  | some i =>
    simp only [physicalFiberInverse, inverseHeight, Pi.smul_apply, Complex.real_smul, one_smul]
    ring

end OAI.Analysis.Calculus.Current
