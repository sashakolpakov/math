import OAI.Analysis.Calculus.Quaternion.Algebra

/-! Actual differential product rules for quaternionic currents. -/

noncomputable section
namespace OAI.Analysis.Calculus.Quaternion

open scoped Matrix Matrix.Norms.Elementwise

section Algebra
variable {m s : Type*} [Fintype m] [Fintype s]

theorem strongDivergence_add (e : s → Q) (dA dB : m × s → Matrix m m Q) (b : m) :
    strongDivergence e (fun p => dA p + dB p) b =
      strongDivergence e dA b + strongDivergence e dB b := by
  simp [strongDivergence, mul_add, Finset.sum_add_distrib]

theorem strongDivergence_smul (e : s → Q) (dA : m × s → Matrix m m Q)
    (c : ℝ) (b : m) :
    strongDivergence e (fun p => c • dA p) b = c • strongDivergence e dA b := by
  simp [strongDivergence, Finset.smul_sum]

theorem strongDivergence_weighted (e : s → Q) (A : Matrix m m Q)
    (dA : m × s → Matrix m m Q) (g : ℝ) (dg : m × s → ℝ) (b : m) :
    strongDivergence e (fun p => dg p • A + g • dA p) b =
      (star (gradientMap e dg) ᵥ* A) b + g • strongDivergence e dA b := by
  rw [strongDivergence_add, strongDivergence_smul]
  congr 1
  simp [strongDivergence, Matrix.vecMul, dotProduct, gradientMap, Finset.sum_mul]

end Algebra

section Differential
variable {E m s : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype m] [Fintype s]

private theorem fderiv_real_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → ℝ} {A : E → F} {x : E}
    (hg : DifferentiableAt ℝ g x) (hA : DifferentiableAt ℝ A x) (v : E) :
    fderiv ℝ (fun y => g y • A y) x v =
      fderiv ℝ g x v • A x + g x • fderiv ℝ A x v := by
  have hF := (hg.hasFDerivAt.smul hA.hasFDerivAt).fderiv
  simpa only [add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, add_comm] using! congrArg (fun L => L v) hF

theorem fderiv_current_smul {g : E → ℝ} {A : E → Matrix m m Q} {x : E}
    (hg : DifferentiableAt ℝ g x) (hA : DifferentiableAt ℝ A x) (v : E) :
    fderiv ℝ (fun y => g y • A y) x v =
      fderiv ℝ g x v • A x + g x • fderiv ℝ A x v := by
  exact fderiv_real_smul hg hA v

theorem strongDivergence_current_smul (e : s → Q) (d : m × s → E)
    {g : E → ℝ} {A : E → Matrix m m Q} {x : E}
    (hg : DifferentiableAt ℝ g x) (hA : DifferentiableAt ℝ A x) (b : m) :
    strongDivergence e (fun p => fderiv ℝ (fun y => g y • A y) x (d p)) b =
      (star (gradientMap e (fun p => fderiv ℝ g x (d p))) ᵥ* A x) b +
        g x • strongDivergence e (fun p => fderiv ℝ A x (d p)) b := by
  simp only [fderiv_current_smul hg hA]
  exact strongDivergence_weighted e (A x) _ (g x) _ b

/-- Multiplication by a real function preserves current conservation whenever
the current annihilates its quaternionic gradient. -/
theorem strongDivergence_current_smul_zero (e : s → Q) (d : m × s → E)
    {g : E → ℝ} {A : E → Matrix m m Q} {x : E}
    (hg : DifferentiableAt ℝ g x) (hA : DifferentiableAt ℝ A x)
    (hG : star (gradientMap e (fun p => fderiv ℝ g x (d p))) ᵥ* A x = 0)
    (hdiv : ∀ b, strongDivergence e (fun p => fderiv ℝ A x (d p)) b = 0) (b : m) :
    strongDivergence e (fun p => fderiv ℝ (fun y => g y • A y) x (d p)) b = 0 := by
  rw [strongDivergence_current_smul e d hg hA, hG, hdiv]
  simp

end Differential
end OAI.Analysis.Calculus.Quaternion
