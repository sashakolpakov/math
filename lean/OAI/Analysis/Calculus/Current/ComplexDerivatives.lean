import OAI.Analysis.Calculus.Current.Coefficients

namespace OAI.Analysis.Calculus.Current

noncomputable section

theorem hasDerivAt_holomorphic_line {d : ℕ} (f : (Index d → ℂ) → ℂ)
    (z V : Index d → ℂ) (hf : DifferentiableAt ℂ f z) :
    HasDerivAt (fun t : ℝ => f (imaginaryLine z V t)) ((fderiv ℂ f z) V) 0 := by
  have hline : HasDerivAt (fun t : ℂ => z + t • V) V 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const V).const_add z
  have hf' : HasFDerivAt f (fderiv ℂ f z) (z + (0 : ℂ) • V) := by
    simpa using hf.hasFDerivAt
  have hh := (hf'.comp_hasDerivAt 0 hline).comp_ofReal
  convert hh using 1
  funext t
  congr 1

theorem complexBarDirectional_holomorphic {d : ℕ} (f : (Index d → ℂ) → ℂ)
    (z V : Index d → ℂ) (hf : DifferentiableAt ℂ f z) :
    complexBarDirectional f z V = 0 := by
  unfold complexBarDirectional
  rw [(hasDerivAt_holomorphic_line f z V hf).deriv,
    (hasDerivAt_holomorphic_line f z (fun a => Complex.I * V a) hf).deriv]
  change (fderiv ℂ f z) V + Complex.I * (fderiv ℂ f z) (Complex.I • V) = 0
  rw [map_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, Complex.I_mul_I]
  ring

theorem barD_holomorphic {d : ℕ} (f : (Index d → ℂ) → ℂ)
    (z : Index d → ℂ) (hf : DifferentiableAt ℂ f z) (a : Index d) :
    barD f z a = 0 := by
  have hh := complexBarDirectional_holomorphic f z (Pi.single a 1) hf
  have hI : (fun b => Complex.I * (Pi.single a 1 : Index d → ℂ) b) =
      Pi.single a Complex.I := by
    ext b
    by_cases h : b = a
    · subst b
      simp
    · simp [Pi.single_eq_of_ne h]
  simpa only [complexBarDirectional, hI, barD] using hh

theorem barD_tangentField {d : ℕ} (v : Fin d → ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) (a b : Index d) :
    barD (fun w => tangentField v w b) z a = 0 :=
  barD_holomorphic _ z (differentiableAt_tangentField_complex v z hY b) a

/-- The diagonal current's antiholomorphic divergence vanishes. -/
theorem diagonal_current_barD_divergence {d : ℕ} (κ : ℝ) (v : Fin d → ℝ)
    (z : Index d → ℂ) (hY : z none ≠ 0) (b : Index d) :
    (∑ a, barD (fun w => (star (tangentField v w a) *
      (gaussianField κ κ v v w : ℂ)) * tangentField v w b) z a) = 0 := by
  have hg : DifferentiableAt ℝ (fun w => (gaussianField κ κ v v w : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z
      (differentiableAt_gaussianField κ κ v v z hY)
  simp_rw [barD_mul _ _ z
    (((differentiableAt_tangentField v z hY _).star).fun_mul hg)
    (differentiableAt_tangentField v z hY b), barD_tangentField v z hY,
    mul_zero, add_zero]
  rw [← Finset.sum_mul, weighted_tangentField_divergence κ κ v v z hY]
  have ht : ∑ a, phaseRow (fun i => (v i : ℂ)) a * tangentField v z a = 0 :=
    phase_tangent _ _
  rw [ht]
  ring

end
end OAI.Analysis.Calculus.Current
