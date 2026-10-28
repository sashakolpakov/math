import OAI.Analysis.Fourier.Radial.Sphere.Decay
import OAI.Analysis.Fourier.Restriction.Outgoing

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff

def outgoingCoefficient (A B : ℝ) : ℂ := ((A : ℂ) - Complex.I * (B : ℂ)) / 2

theorem outgoingCoefficient_ne_zero {A B : ℝ} (h : 0 < A^2+B^2) :
    outgoingCoefficient A B ≠ 0 :=
  div_ne_zero (OAI.Analysis.Fourier.Restriction.outgoing_coefficient_ne_zero h) (by norm_num)

/-- The two spherical stationary phases have conjugate nonzero coefficients. -/
theorem two_phase_identity (A B r : ℝ) :
    ((A * Real.cos r + B * Real.sin r : ℝ) : ℂ) =
      outgoingCoefficient A B * Complex.exp (Complex.I * (r : ℂ)) +
      star (outgoingCoefficient A B) * Complex.exp (-Complex.I * (r : ℂ)) := by
  rw [show Complex.I * (r : ℂ) = (r : ℂ) * Complex.I by ring,
    show -Complex.I * (r : ℂ) = ((-r : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  apply Complex.ext <;>
    simp [outgoingCoefficient, Complex.mul_re, Complex.mul_im] <;> ring

/-- The actual unit-sphere Fourier integral has a nonvanishing outgoing
coefficient and a uniform normalized error of order one inverse radius. -/
theorem sphere_two_phase_asymptotic {n : ℕ} (hn : 1 ≤ n) :
    ∃ c : ℂ, c ≠ 0 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Space n, 1 ≤ ‖x‖ →
      ‖((‖x‖ ^ (((n : ℝ)-1)/2) : ℝ) : ℂ) *
          OAI.Analysis.Fourier.Restriction.sphericalExtension (fun _ : Space n => (1 : ℂ)) x -
        (c * Complex.exp (Complex.I * (‖x‖ : ℂ)) +
          star c * Complex.exp (-Complex.I * (‖x‖ : ℂ)))‖ ≤ C / ‖x‖ := by
  obtain ⟨A,B,C,hC,hAB,h⟩ := OAI.Analysis.Fourier.Radial.sphericalExtension_one_asymptotic hn
  refine ⟨outgoingCoefficient A B,outgoingCoefficient_ne_zero hAB,C,hC,?_⟩
  intro x hx
  rw [← two_phase_identity]
  exact h x hx

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
