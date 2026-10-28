import OAI.Analysis.Calculus.Current.Cancellation

namespace OAI.Analysis.Calculus.Current

noncomputable section

theorem barD_add {d : ℕ} (f g : (Index d → ℂ) → ℂ) (z : Index d → ℂ)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (a : Index d) :
    barD (fun w => f w + g w) z a = barD f z a + barD g z a := by
  have h1 := (hasDerivAt_function_line f z (Pi.single a 1) hf).fun_add
    (hasDerivAt_function_line g z (Pi.single a 1) hg)
  have hi := (hasDerivAt_function_line f z (Pi.single a Complex.I) hf).fun_add
    (hasDerivAt_function_line g z (Pi.single a Complex.I) hg)
  simp only [barD, h1.deriv, hi.deriv,
    deriv_imaginaryLine f z _ hf, deriv_imaginaryLine g z _ hg]
  ring

theorem barD_sub {d : ℕ} (f g : (Index d → ℂ) → ℂ) (z : Index d → ℂ)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (a : Index d) :
    barD (fun w => f w - g w) z a = barD f z a - barD g z a := by
  have h1 := (hasDerivAt_function_line f z (Pi.single a 1) hf).fun_sub
    (hasDerivAt_function_line g z (Pi.single a 1) hg)
  have hi := (hasDerivAt_function_line f z (Pi.single a Complex.I) hf).fun_sub
    (hasDerivAt_function_line g z (Pi.single a Complex.I) hg)
  simp only [barD, h1.deriv, hi.deriv,
    deriv_imaginaryLine f z _ hf, deriv_imaginaryLine g z _ hg]
  ring

theorem barD_const {d : ℕ} (c : ℂ) (z : Index d → ℂ) (a : Index d) :
    barD (fun _ => c) z a = 0 := by simp [barD]

theorem barD_mul_const {d : ℕ} (f : (Index d → ℂ) → ℂ) (c : ℂ) (z : Index d → ℂ)
    (hf : DifferentiableAt ℝ f z) (a : Index d) :
    barD (fun w => f w * c) z a = barD f z a * c := by
  rw [barD_mul _ _ z hf (differentiableAt_const c), barD_const]
  ring

theorem complexBarDirectional_mul {d : ℕ} (f g : (Index d → ℂ) → ℂ)
    (z V : Index d → ℂ) (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    complexBarDirectional (fun w => f w * g w) z V =
      complexBarDirectional f z V * g z + f z * complexBarDirectional g z V := by
  rw [complexBarDirectional_eq_sum _ z V (hf.fun_mul hg),
    complexBarDirectional_eq_sum _ z V hf, complexBarDirectional_eq_sum _ z V hg]
  simp_rw [barD_mul _ _ z hf hg]
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem gaussianField_swap {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ) :
    gaussianField κ κ' v v' = gaussianField κ' κ v' v := by
  funext z
  unfold gaussianField gaussianPair gaussianLog
  congr 2
  ring

theorem differentiableAt_gaussianField_complex {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (z : Index d → ℂ) (hY : z none ≠ 0) :
    DifferentiableAt ℝ (fun w => (gaussianField κ κ' v v' w : ℂ)) z :=
  Complex.ofRealCLM.differentiableAt.comp z
    (differentiableAt_gaussianField κ κ' v v' z hY)

/-- Product rule for a weighted vector, retaining the actual differential
operator on the arbitrary smooth scalar factor. -/
theorem weighted_tangentField_product_divergence {d : ℕ} (κ κ' : ℝ)
    (v v' : Fin d → ℝ) (f : (Index d → ℂ) → ℂ)
    (z : Index d → ℂ) (hY : z none ≠ 0) (hf : DifferentiableAt ℝ f z) :
    (∑ a, barD (fun w => (star (tangentField v w a) *
      (gaussianField κ κ' v v' w : ℂ)) * f w) z a) =
      ((gaussianField κ κ' v v' z : ℂ) * movingUnit z * (κ' : ℂ) *
        ∑ a, phaseRow (fun i => (v' i : ℂ)) a * tangentField v z a) * f z +
      (gaussianField κ κ' v v' z : ℂ) * complexBarDirectional f z (tangentField v z) := by
  have hg := differentiableAt_gaussianField_complex κ κ' v v' z hY
  have ha (a : Index d) := barD_mul
    (fun w => star (tangentField v w a) * (gaussianField κ κ' v v' w : ℂ)) f z
      (((differentiableAt_tangentField v z hY a).star).fun_mul hg) hf a
  simp_rw [ha]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul,
    weighted_tangentField_divergence κ κ' v v' z hY,
    complexBarDirectional_eq_sum _ z _ hf]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

end
end OAI.Analysis.Calculus.Current
