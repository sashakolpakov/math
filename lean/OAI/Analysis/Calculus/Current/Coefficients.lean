import OAI.Analysis.Calculus.Current.Wirtinger

/-! Actual coordinate derivatives of the current's holomorphic coefficient vector. -/

namespace OAI.Analysis.Calculus.Current

noncomputable section

def tangentField {d : ℕ} (v : Fin d → ℝ) (z : Index d → ℂ) : Index d → ℂ :=
  tangentVector (fun i => (v i : ℂ)) (ratio z)

def tangentSelfSlope {d : ℕ} (z : Index d → ℂ) (c : ℂ) : Index d → ℂ
  | none => 0
  | some none => 0
  | some (some _) => c / (2 * z none)

theorem hasDerivAt_tangentField_coordinate {d : ℕ} (v : Fin d → ℝ)
    (z : Index d → ℂ) (a : Index d) (c : ℂ) :
    HasDerivAt
      (fun q : ℂ => tangentField v (fun b => z b + q * (Pi.single a c : Index d → ℂ) b) a)
      (tangentSelfSlope z c a) 0 := by
  cases a with
  | none =>
    simpa [tangentField, tangentVector, tangentSelfSlope] using
      hasDerivAt_const (0 : ℂ) (1 : ℂ)
  | some a =>
    cases a with
    | none =>
      simpa [tangentField, tangentVector, tangentSelfSlope, ratio, Pi.single_apply] using
        hasDerivAt_const (0 : ℂ)
          (-(∑ i, (z (some (some i)) / z none) * (v i : ℂ)) / 2)
    | some i =>
      have hh := (((((hasDerivAt_id (0 : ℂ)).mul_const c).const_add
        (z (some (some i)))).div_const (z none)).const_add (v i : ℂ)).div_const 2
      convert hh using 1
      · funext q
        simp [tangentField, tangentVector, ratio]
      · simp only [tangentSelfSlope, one_mul]
        ring

theorem barD_conjugate_tangentField_self {d : ℕ} (v : Fin d → ℝ)
    (z : Index d → ℂ) (a : Index d) :
    barD (fun w => star (tangentField v w a)) z a =
      star (tangentSelfSlope z 2 a) := by
  have hr := (hasDerivAt_tangentField_coordinate v z a 1).comp_ofReal.star
  have hi := (hasDerivAt_tangentField_coordinate v z a Complex.I).comp_ofReal.star
  unfold barD
  rw [show deriv (fun t : ℝ => star (tangentField v (imaginaryLine z (Pi.single a 1) t) a)) 0 =
      star (tangentSelfSlope z 1 a) from hr.deriv]
  rw [show deriv (fun t : ℝ => star (tangentField v (imaginaryLine z (Pi.single a Complex.I) t) a)) 0 =
      star (tangentSelfSlope z Complex.I a) from hi.deriv]
  cases a with
  | none => simp [tangentSelfSlope]
  | some a =>
    cases a with
    | none => simp [tangentSelfSlope]
    | some i =>
      simp only [tangentSelfSlope, star_div₀, star_mul, star_ofNat,
        Complex.star_def, map_one, Complex.conj_I]
      ring_nf
      simp
      ring

/-- Equation (current-derivatives): the coefficient divergence is `d / conj(Y)`. -/
theorem tangentField_coefficient_divergence {d : ℕ} (v : Fin d → ℝ)
    (z : Index d → ℂ) :
    ∑ a, barD (fun w => star (tangentField v w a)) z a = (d : ℂ) / star (z none) := by
  simp only [barD_conjugate_tangentField_self, Fintype.sum_option, tangentSelfSlope]
  simp [div_eq_mul_inv, mul_inv_rev]
  left
  ring

theorem differentiableAt_tangentField_complex {d : ℕ} (v : Fin d → ℝ)
    (z : Index d → ℂ) (hY : z none ≠ 0) (a : Index d) :
    DifferentiableAt ℂ (fun w => tangentField v w a) z := by
  have hratio (i : Fin d) : DifferentiableAt ℂ (fun w => ratio w i) z := by
    unfold ratio
    fun_prop (disch := assumption)
  cases a with
  | none => exact differentiableAt_const _
  | some a =>
    cases a with
    | none =>
      change DifferentiableAt ℂ (fun w => -(∑ i, ratio w i * (v i : ℂ)) / 2) z
      fun_prop
    | some i =>
      change DifferentiableAt ℂ (fun w => ((v i : ℂ) + ratio w i) / 2) z
      fun_prop

theorem differentiableAt_tangentField {d : ℕ} (v : Fin d → ℝ)
    (z : Index d → ℂ) (hY : z none ≠ 0) (a : Index d) :
    DifferentiableAt ℝ (fun w => tangentField v w a) z :=
  (differentiableAt_tangentField_complex v z hY a).restrictScalars ℝ

theorem hasDerivAt_function_line {d : ℕ} (f : (Index d → ℂ) → ℂ)
    (z V : Index d → ℂ) (hf : DifferentiableAt ℝ f z) :
    HasDerivAt (fun t : ℝ => f (imaginaryLine z V t)) ((fderiv ℝ f z) V) 0 := by
  have hf' : HasFDerivAt f (fderiv ℝ f z) (imaginaryLine z V 0) := by
    simpa only [imaginaryLine_zero] using hf.hasFDerivAt
  exact hf'.comp_hasDerivAt 0 (hasDerivAt_imaginaryLine_vector z V)

theorem barD_mul {d : ℕ} (f g : (Index d → ℂ) → ℂ) (z : Index d → ℂ)
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (a : Index d) :
    barD (fun w => f w * g w) z a = barD f z a * g z + f z * barD g z a := by
  have h1 := (hasDerivAt_function_line f z (Pi.single a 1) hf).fun_mul
    (hasDerivAt_function_line g z (Pi.single a 1) hg)
  have hi := (hasDerivAt_function_line f z (Pi.single a Complex.I) hf).fun_mul
    (hasDerivAt_function_line g z (Pi.single a Complex.I) hg)
  simp only [barD, h1.deriv, hi.deriv, imaginaryLine_zero,
    deriv_imaginaryLine f z _ hf, deriv_imaginaryLine g z _ hg]
  ring

/-- The exact weighted coordinate divergence from (current-derivatives), with all
derivatives evaluated on the actual Gaussian and tangent fields. -/
theorem weighted_tangentField_divergence {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (z : Index d → ℂ) (hY : z none ≠ 0) :
    (∑ a, barD (fun w => star (tangentField v w a) *
      (gaussianField κ κ' v v' w : ℂ)) z a) =
      (gaussianField κ κ' v v' z : ℂ) * (z none / (‖z none‖ : ℂ)) *
        (κ' : ℂ) * ∑ a, phaseRow (fun i => (v' i : ℂ)) a * tangentField v z a := by
  have hg : DifferentiableAt ℝ (fun w => (gaussianField κ κ' v v' w : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z
      (differentiableAt_gaussianField κ κ' v v' z hY)
  simp_rw [barD_mul _ _ z ((differentiableAt_tangentField v z hY _).star) hg]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, tangentField_coefficient_divergence]
  have hgcoord := gaussianField_coordinate_identity κ κ' v v' z hY
  change (∑ a, star (tangentField v z a) *
    barD (fun w => (gaussianField κ κ' v v' w : ℂ)) z a) = _ at hgcoord
  rw [hgcoord]
  have hn : (‖z none‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hY
  have hs : star (z none) ≠ 0 := star_ne_zero.mpr hY
  have he : (d : ℂ) / star (z none) =
      (z none / (‖z none‖ : ℂ)) * ((d : ℂ) / (‖z none‖ : ℂ)) := by
    rw [← norm_div_star (z none) hY]
    field_simp
  rw [he]
  dsimp only [tangentField]
  ring

end
end OAI.Analysis.Calculus.Current
