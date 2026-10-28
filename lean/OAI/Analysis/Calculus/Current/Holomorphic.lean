import OAI.Analysis.Calculus.Current.Algebra

/-! The holomorphic background `Φ` used to define the wave current.
This file proves its differential along every complex direction. -/

namespace OAI.Analysis.Calculus.Current

noncomputable section

/-- The holomorphic background `S₁ + (P·P)/(2Y)`. -/
def phi {d : ℕ} (z : Index d → ℂ) : ℂ :=
  z (some none) + (∑ i, z (some (some i)) * z (some (some i))) / (2 * z none)

/-- `W = P/Y` in the imaginary coordinates of the manuscript. -/
def ratio {d : ℕ} (z : Index d → ℂ) : Fin d → ℂ :=
  fun i => z (some (some i)) / z none

private theorem phi_differential_algebra {d : ℕ} (z h : Index d → ℂ)
    (hY : z none ≠ 0) :
    h (some none) +
      ((∑ i : Fin d, (h (some (some i)) * z (some (some i)) +
        z (some (some i)) * h (some (some i)))) * (2 * z none) -
        (∑ i : Fin d, z (some (some i)) * z (some (some i))) * (2 * h none)) /
        (2 * z none) ^ 2 =
      ∑ a, phaseRow (ratio z) a * h a := by
  have hs : (∑ i : Fin d, (z (some (some i)) / z none) *
      (z (some (some i)) / z none)) =
      (∑ i : Fin d, z (some (some i)) * z (some (some i))) / (z none * z none) := by
    simp_rw [div_mul_div_comm]
    rw [Finset.sum_div]
  have hl : (∑ i : Fin d, (z (some (some i)) / z none) * h (some (some i))) =
      (∑ i : Fin d, z (some (some i)) * h (some (some i))) / z none := by
    simp_rw [div_mul_eq_mul_div]
    rw [Finset.sum_div]
  simp only [Fintype.sum_option, phaseRow, ratio, one_mul]
  rw [hs, hl]
  rw [Finset.sum_add_distrib]
  simp_rw [show ∀ i, h (some (some i)) * z (some (some i)) =
    z (some (some i)) * h (some (some i)) from fun _ => mul_comm _ _]
  field_simp
  ring

/-- Equation (Phi-derivative): the differential is exactly the phase row `ℓ(W)`.
The direction is arbitrary and the only restriction is the stated domain `Y ≠ 0`. -/
theorem hasDerivAt_phi_line {d : ℕ} (z h : Index d → ℂ) (hY : z none ≠ 0) :
    HasDerivAt (fun q : ℂ => phi (fun a => z a + q * h a))
      (∑ a, phaseRow (ratio z) a * h a) 0 := by
  have hz (a : Index d) :
      HasDerivAt (fun q : ℂ => z a + q * h a) (h a) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (h a)).const_add (z a)
  have hp := HasDerivAt.fun_sum (u := Finset.univ) (fun (i : Fin d) _ =>
    (hz (some (some i))).mul (hz (some (some i))))
  have hy := (hz none).const_mul (2 : ℂ)
  have hden : 2 * (z none + (0 : ℂ) * h none) ≠ 0 := by
    simpa using mul_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0) hY
  have hh := (hz (some none)).add (hp.div hy hden)
  convert hh using 1
  · funext q
    simp [phi]
  · simpa only [Pi.mul_apply, zero_mul, add_zero] using
      (phi_differential_algebra z h hY).symm

/-- `Φ` is holomorphic everywhere in its stated domain. -/
theorem differentiableAt_phi {d : ℕ} (z : Index d → ℂ) (hY : z none ≠ 0) :
    DifferentiableAt ℂ (phi : (Index d → ℂ) → ℂ) z := by
  unfold phi
  fun_prop (disch := exact mul_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0) hY)

/-- Each current vector has zero derivative against the actual background `Φ`. -/
theorem hasDerivAt_phi_tangent {d : ℕ} (z : Index d → ℂ)
    (hY : z none ≠ 0) (v : Fin d → ℂ) :
    HasDerivAt
      (fun q : ℂ => phi (fun a => z a + q * tangentVector v (ratio z) a)) 0 0 := by
  simpa only [background_tangent] using
    hasDerivAt_phi_line z (tangentVector v (ratio z)) hY

end
end OAI.Analysis.Calculus.Current
