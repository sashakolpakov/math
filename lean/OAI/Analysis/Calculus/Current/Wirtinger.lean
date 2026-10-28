import OAI.Analysis.Calculus.Current.Divergence

/-! Coordinate Wirtinger operators and their relation to real directional derivatives. -/

namespace OAI.Analysis.Calculus.Current

noncomputable section

def complexBarDirectional {d : ℕ} (f : (Index d → ℂ) → ℂ)
    (z V : Index d → ℂ) : ℂ :=
  deriv (fun t : ℝ => f (imaginaryLine z V t)) 0 +
    Complex.I * deriv (fun t : ℝ => f (imaginaryLine z (fun a => Complex.I * V a) t)) 0

/-- `∂p + i∂q`, which is twice the antiholomorphic Wirtinger derivative. -/
def barD {d : ℕ} (f : (Index d → ℂ) → ℂ) (z : Index d → ℂ) (a : Index d) : ℂ :=
  deriv (fun t : ℝ => f (imaginaryLine z (Pi.single a 1) t)) 0 +
    Complex.I * deriv (fun t : ℝ => f (imaginaryLine z (Pi.single a Complex.I) t)) 0

theorem hasDerivAt_imaginaryLine_vector {d : ℕ} (z V : Index d → ℂ) :
    HasDerivAt (imaginaryLine z V) V 0 := by
  have hh := ((hasDerivAt_id (0 : ℝ)).smul_const V).const_add z
  convert hh using 1
  · funext t a
    simp [imaginaryLine, Complex.real_smul]
  · simp

theorem deriv_imaginaryLine {d : ℕ} (f : (Index d → ℂ) → ℂ)
    (z V : Index d → ℂ) (hf : DifferentiableAt ℝ f z) :
    deriv (fun t : ℝ => f (imaginaryLine z V t)) 0 = (fderiv ℝ f z) V := by
  have hf' : HasFDerivAt f (fderiv ℝ f z) (imaginaryLine z V 0) := by
    simpa only [imaginaryLine_zero] using hf.hasFDerivAt
  have hh := hf'.comp_hasDerivAt 0 (hasDerivAt_imaginaryLine_vector z V)
  simpa only [imaginaryLine_zero, Function.comp_def] using hh.deriv

private theorem single_complex_split {d : ℕ} (a : Index d) (c : ℂ) :
    Pi.single a c = c.re • (Pi.single a (1 : ℂ) : Index d → ℂ) +
      c.im • (Pi.single a Complex.I : Index d → ℂ) := by
  ext b
  by_cases h : b = a
  · subst b
    simp only [Pi.single_eq_same, Pi.add_apply, Pi.smul_apply, Complex.real_smul, mul_one]
    apply Complex.ext <;> simp
  · simp [Pi.single_eq_of_ne h]

private theorem realLinear_single_pair {d : ℕ} (F : (Index d → ℂ) →L[ℝ] ℂ)
    (a : Index d) (c : ℂ) :
    F (Pi.single a c) + Complex.I * F (Pi.single a (Complex.I * c)) =
      star c * (F (Pi.single a 1) + Complex.I * F (Pi.single a Complex.I)) := by
  rw [single_complex_split a c, single_complex_split a (Complex.I * c)]
  simp only [map_add, map_smul, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, zero_add]
  have hc : star c = (c.re : ℂ) - Complex.I * (c.im : ℂ) := by
    apply Complex.ext <;> simp
  rw [hc]
  push_cast
  ring_nf
  simp

theorem realLinear_barDirectional {d : ℕ} (F : (Index d → ℂ) →L[ℝ] ℂ)
    (V : Index d → ℂ) :
    F V + Complex.I * F (fun a => Complex.I * V a) =
      ∑ a, star (V a) * (F (Pi.single a 1) + Complex.I * F (Pi.single a Complex.I)) := by
  conv_lhs =>
    arg 1
    rw [← Finset.univ_sum_single V, map_sum]
  conv_lhs =>
    arg 2
    arg 2
    rw [← Finset.univ_sum_single (fun a => Complex.I * V a), map_sum]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  exact realLinear_single_pair F a (V a)

/-- The two real directional derivatives equal exactly the manuscript's weighted
coordinate operator `∑ conj(Vₐ) barDₐ`. -/
theorem complexBarDirectional_eq_sum {d : ℕ} (f : (Index d → ℂ) → ℂ)
    (z V : Index d → ℂ) (hf : DifferentiableAt ℝ f z) :
    complexBarDirectional f z V = ∑ a, star (V a) * barD f z a := by
  simp only [complexBarDirectional, barD, deriv_imaginaryLine f z _ hf]
  exact realLinear_barDirectional _ _

theorem differentiableAt_gaussianField {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (z : Index d → ℂ) (hY : z none ≠ 0) :
    DifferentiableAt ℝ (gaussianField κ κ' v v') z := by
  have hn : ‖z none‖ ≠ 0 := norm_ne_zero_iff.mpr hY
  have hy : DifferentiableAt ℝ (fun w : Index d → ℂ => ‖w none‖) z :=
    (differentiableAt_apply none z).norm ℂ hY
  have hs (w : Fin d → ℝ) :
      DifferentiableAt ℝ (fun q => squaredDistance (ratio q) w) z := by
    apply DifferentiableAt.fun_sum
    intro i _
    apply DifferentiableAt.norm_sq (𝕜 := ℂ)
    unfold ratio
    simpa only [div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply] using
      ((differentiableAt_apply (𝕜 := ℝ) (some (some i)) z).mul
        ((differentiableAt_apply (𝕜 := ℝ) none z).inv hY)).sub_const (w i : ℂ)
  have hsv := hs v
  have hsv' := hs v'
  unfold gaussianField gaussianPair gaussianLog
  fun_prop (disch := assumption)

theorem complexBarDirectional_gaussianField {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (z V : Index d → ℂ) (hY : z none ≠ 0) :
    complexBarDirectional (fun w => (gaussianField κ κ' v v' w : ℂ)) z V =
      barDirectional (gaussianField κ κ' v v') z V := by
  unfold complexBarDirectional barDirectional
  rw [(hasDerivAt_gaussianField_line κ κ' v v' z V hY).ofReal_comp.deriv,
    (hasDerivAt_gaussianField_line κ κ' v v' z (fun a => Complex.I * V a) hY).ofReal_comp.deriv,
    (hasDerivAt_gaussianField_line κ κ' v v' z V hY).deriv,
    (hasDerivAt_gaussianField_line κ κ' v v' z (fun a => Complex.I * V a) hY).deriv]

/-- The exact coordinate differential identity for the cross-mode Gaussian weight. -/
theorem gaussianField_coordinate_identity {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (z : Index d → ℂ) (hY : z none ≠ 0) :
    let V := tangentVector (fun i => (v i : ℂ)) (ratio z)
    (∑ a, star (V a) * barD (fun w => (gaussianField κ κ' v v' w : ℂ)) z a) =
      (gaussianField κ κ' v v' z : ℂ) * (z none / (‖z none‖ : ℂ)) *
        (-(d : ℂ) / (‖z none‖ : ℂ) +
          (κ' : ℂ) * ∑ a, phaseRow (fun i => (v' i : ℂ)) a * V a) := by
  dsimp only
  have hf : DifferentiableAt ℝ (fun w => (gaussianField κ κ' v v' w : ℂ)) z := by
    exact Complex.ofRealCLM.differentiableAt.comp z
      (differentiableAt_gaussianField κ κ' v v' z hY)
  rw [← complexBarDirectional_eq_sum _ z _ hf,
    complexBarDirectional_gaussianField κ κ' v v' z _ hY]
  exact gaussianField_tangent_derivative κ κ' v v' z hY

end
end OAI.Analysis.Calculus.Current
