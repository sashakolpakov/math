import OAI.Analysis.PDE.Dirichlet.Gradient
import OAI.LinearAlgebra.Moore.Square

open Set
open scoped Matrix ComplexOrder

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

/-- A data-only lower bound for the linearization in the identity direction. -/
theorem mooreDifferential_one_lower {n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hA : (OAI.LinearAlgebra.Moore.complexify A).PosDef)
    {M : ℝ} (hM : OAI.LinearAlgebra.Moore.mooreDet n A ≤ M) :
    OAI.LinearAlgebra.Moore.mooreDet n A / (2 * (M ^ 2 + 1)) ≤ OAI.LinearAlgebra.Moore.mooreDifferential n A 1 := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨C, hAC, hCA⟩ := OAI.LinearAlgebra.Moore.exists_quaternion_inverse_of_complexify_posDef A hA
  have hC := OAI.LinearAlgebra.Moore.complexify_inverse_posDef n A C hA hAC
  have hac : OAI.LinearAlgebra.Moore.complexify A * OAI.LinearAlgebra.Moore.complexify C = 1 := by
    rw [← OAI.LinearAlgebra.Moore.complexify_mul, hAC, OAI.LinearAlgebra.Moore.complexify_one]
  have hpos := OAI.LinearAlgebra.Moore.mooreDet_pos_of_complexify_posDef A hA
  have hmb : (OAI.LinearAlgebra.Moore.complexify A).det.re ≤ M ^ 2 := by
    rw [← OAI.LinearAlgebra.Moore.mooreDet_sq_eq_complexify_det_of_posDef A hA]
    nlinarith
  have ht := complex_inverse_trace_lower (OAI.LinearAlgebra.Moore.complexify A) (OAI.LinearAlgebra.Moore.complexify C) hA hC hac hmb
  rw [OAI.LinearAlgebra.Moore.complexify_trace_real] at ht
  rw [OAI.LinearAlgebra.Moore.mooreDifferential_inverse n A 1 C (OAI.LinearAlgebra.Moore.isHermitian_of_complexify hA.isHermitian)
    (by simp) hAC hCA, Matrix.mul_one]
  have hden : 0 < M ^ 2 + 1 := by positivity
  have ht' := (div_le_iff₀ hden).mp ht
  have hm := mul_le_mul_of_nonneg_left ht' hpos.le
  apply (div_le_iff₀ (by positivity : 0 < 2 * (M ^ 2 + 1))).mpr
  nlinarith

/-- Uniform strict convexity of the defining function and upper/lower bounds
on the determinant give a uniform lower bound for its linearization. -/
theorem mooreDifferential_defining_lower {n : ℕ} (hn : 1 ≤ n)
    (A R : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hA : (OAI.LinearAlgebra.Moore.complexify A).PosDef)
    {m M r₀ : ℝ} (hr₀ : 0 < r₀) (hmin : m ≤ OAI.LinearAlgebra.Moore.mooreDet n A) (hmax : OAI.LinearAlgebra.Moore.mooreDet n A ≤ M)
    (hR : (OAI.LinearAlgebra.Moore.complexify (R - r₀ • (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)))).PosSemidef) :
    r₀ * (m / (2 * (M ^ 2 + 1))) ≤ OAI.LinearAlgebra.Moore.mooreDifferential n A R := by
  have hI := mooreDifferential_one_lower hn A hA hmax
  have hquot : m / (2 * (M ^ 2 + 1)) ≤ OAI.LinearAlgebra.Moore.mooreDet n A / (2 * (M ^ 2 + 1)) :=
    div_le_div_of_nonneg_right hmin (by positivity)
  have hbound := mul_le_mul_of_nonneg_left (hquot.trans hI) hr₀.le
  have hdiff := OAI.LinearAlgebra.Moore.mooreDifferential_nonneg_of_posDef A (R - r₀ • 1) hA hR
  have hsplit : OAI.LinearAlgebra.Moore.mooreDifferential n A R =
      OAI.LinearAlgebra.Moore.mooreDifferential n A (R - r₀ • 1) + r₀ * OAI.LinearAlgebra.Moore.mooreDifferential n A 1 := by
    calc
      OAI.LinearAlgebra.Moore.mooreDifferential n A R = OAI.LinearAlgebra.Moore.mooreDifferential n A ((R - r₀ • 1) + r₀ • 1) := by
        rw [sub_add_cancel]
      _ = _ := by rw [OAI.LinearAlgebra.Moore.mooreDifferential_add, OAI.LinearAlgebra.Moore.mooreDifferential_smul]
  rw [hsplit]
  linarith

/-- A genuine first-derivative a priori estimate whose interior constants use
only the prescribed right-hand side and the defining function. -/
theorem quaternionic_gradient_estimate {n : ℕ} (hn : 1 ≤ n)
    {K : Set (CoordinateSpace n 4)} (hK : IsCompact K)
    {ψ r F : CoordinateSpace n 4 → ℝ} (hψ : ContDiff ℝ 3 ψ) (hr : ContDiff ℝ 2 r)
    (hF : DifferentiableOn ℝ F (interior K))
    (hA : ∀ x ∈ interior K, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (heq : ∀ x ∈ interior K, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = F x)
    (v : CoordinateSpace n 4) {m M r₀ L B : ℝ} (hm : 0 < m) (hr₀ : 0 < r₀) (hL : 0 ≤ L)
    (hdataBounds : ∀ x ∈ interior K, m ≤ F x ∧ F x ≤ M)
    (hconvex : ∀ x ∈ interior K,
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)))).PosSemidef)
    (hdata : ∀ x ∈ interior K, |directionalDerivative F v x| ≤ L)
    (hboundary : ∀ x ∈ K, x ∉ interior K → |directionalDerivative ψ v x| ≤ B)
    (hrbd : ∀ x ∈ K, x ∉ interior K → r x = 0) :
    ∀ x ∈ K, |directionalDerivative ψ v x| ≤
      B - (L / (r₀ * (m / (2 * (M ^ 2 + 1))))) * r x := by
  apply quaternionic_gradient_estimate_of_barrier_coercivity hn hK hψ hr hF hA heq v
    (by positivity) hL ?_ hdata hboundary hrbd
  intro x hx
  apply mooreDifferential_defining_lower hn _ _ (hA x hx) hr₀
  · rw [heq x hx]
    exact (hdataBounds x hx).1
  · rw [heq x hx]
    exact (hdataBounds x hx).2
  · exact hconvex x hx

/-- Norm form of the data-only interior first-derivative estimate. -/
theorem quaternionic_gradient_norm_estimate {n : ℕ} (hn : 1 ≤ n)
    {K : Set (CoordinateSpace n 4)} (hK : IsCompact K)
    {ψ r F : CoordinateSpace n 4 → ℝ} (hψ : ContDiff ℝ 3 ψ) (hr : ContDiff ℝ 2 r)
    (hF : DifferentiableOn ℝ F (interior K))
    (hA : ∀ x ∈ interior K, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (heq : ∀ x ∈ interior K, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = F x)
    {m M r₀ L B : ℝ} (hm : 0 < m) (hr₀ : 0 < r₀) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hdataBounds : ∀ x ∈ interior K, m ≤ F x ∧ F x ≤ M)
    (hconvex : ∀ x ∈ interior K,
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)))).PosSemidef)
    (hdata : ∀ x ∈ interior K, ‖fderiv ℝ F x‖ ≤ L)
    (hboundary : ∀ x ∈ K, x ∉ interior K → ‖fderiv ℝ ψ x‖ ≤ B)
    (hrbd : ∀ x ∈ K, x ∉ interior K → r x = 0)
    (hrnonpos : ∀ x ∈ K, r x ≤ 0) :
    ∀ x ∈ K, ‖fderiv ℝ ψ x‖ ≤ B - (L / (r₀ * (m / (2 * (M ^ 2 + 1))))) * r x := by
  let κ : ℝ := r₀ * (m / (2 * (M ^ 2 + 1)))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  intro x hx
  change ‖fderiv ℝ ψ x‖ ≤ B - (L / κ) * r x
  apply ContinuousLinearMap.opNorm_le_bound _ (by
    have : (L / κ) * r x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (div_nonneg hL hκ.le) (hrnonpos x hx)
    linarith)
  intro v
  have hd : ∀ y ∈ interior K, |directionalDerivative F v y| ≤ L * ‖v‖ := by
    intro y hy
    calc
      |directionalDerivative F v y| ≤ ‖fderiv ℝ F y‖ * ‖v‖ := by
        simpa only [directionalDerivative, Real.norm_eq_abs] using ContinuousLinearMap.le_opNorm (fderiv ℝ F y) v
      _ ≤ L * ‖v‖ := mul_le_mul_of_nonneg_right (hdata y hy) (norm_nonneg v)
  have hb : ∀ y ∈ K, y ∉ interior K → |directionalDerivative ψ v y| ≤ B * ‖v‖ := by
    intro y hy hyi
    calc
      |directionalDerivative ψ v y| ≤ ‖fderiv ℝ ψ y‖ * ‖v‖ := by
        simpa only [directionalDerivative, Real.norm_eq_abs] using ContinuousLinearMap.le_opNorm (fderiv ℝ ψ y) v
      _ ≤ B * ‖v‖ := mul_le_mul_of_nonneg_right (hboundary y hy hyi) (norm_nonneg v)
  have hv := quaternionic_gradient_estimate hn hK hψ hr hF hA heq v hm hr₀
    (mul_nonneg hL (norm_nonneg v)) hdataBounds hconvex hd hb hrbd x hx
  change |directionalDerivative ψ v x| ≤ B * ‖v‖ - ((L * ‖v‖) / κ) * r x at hv
  rw [show B * ‖v‖ - ((L * ‖v‖) / κ) * r x = (B - (L / κ) * r x) * ‖v‖ by ring] at hv
  simpa only [directionalDerivative, Real.norm_eq_abs] using hv

end OAI.Analysis.PDE.Dirichlet
