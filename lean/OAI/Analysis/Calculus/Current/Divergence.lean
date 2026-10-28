import OAI.Analysis.Calculus.Current.Holomorphic

/-! Differential ingredients for the wave-current divergence calculation.
The Gaussian pair is defined by its actual scalar expression. The calculus
lemmas take ordinary derivative certificates for input curves; they do not
assume the weighted conservation identity to be proved.
-/

namespace OAI.Analysis.Calculus.Current

noncomputable section

def squaredDistance {d : ℕ} (W : Fin d → ℂ) (v : Fin d → ℝ) : ℝ :=
  ∑ i, ‖W i - (v i : ℂ)‖ ^ 2

def gaussianLog {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (y : ℝ) (W : Fin d → ℂ) : ℝ :=
  -(d : ℝ) * Real.log y -
    y / 2 * (κ * squaredDistance W v + κ' * squaredDistance W v')

/-- The pair weight `N` of equation (current-gaussian-pair), on `y > 0`. -/
def gaussianPair {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (y : ℝ) (W : Fin d → ℂ) : ℝ := Real.exp (gaussianLog κ κ' v v' y W)

theorem gaussianPair_formula {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (y : ℝ) (hy : 0 < y) (W : Fin d → ℂ) :
    gaussianPair κ κ' v v' y W = (y ^ d)⁻¹ *
      Real.exp (-(y / 2 * (κ * squaredDistance W v + κ' * squaredDistance W v'))) := by
  unfold gaussianPair gaussianLog
  rw [sub_eq_add_neg, Real.exp_add]
  congr 1
  rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hy]

theorem gaussianPair_pos {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (y : ℝ) (W : Fin d → ℂ) : 0 < gaussianPair κ κ' v v' y W :=
  Real.exp_pos _

/-- Differentiate the exact Euclidean squared distance along an arbitrary real curve. -/
theorem hasDerivAt_squaredDistance {d : ℕ} (W : ℝ → Fin d → ℂ)
    (W' : Fin d → ℂ) (v : Fin d → ℝ) (t : ℝ)
    (hW : ∀ i, HasDerivAt (fun s => W s i) (W' i) t) :
    HasDerivAt (fun s => squaredDistance (W s) v)
      (∑ i, 2 * inner ℝ (W t i - (v i : ℂ)) (W' i)) t := by
  exact HasDerivAt.fun_sum fun i _ => ((hW i).sub_const (v i : ℂ)).norm_sq

/-- Ordinary derivative of the exact logarithmic Gaussian pair. -/
theorem hasDerivAt_gaussianLog {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (y : ℝ → ℝ) (y' : ℝ) (W : ℝ → Fin d → ℂ) (W' : Fin d → ℂ) (t : ℝ)
    (hy : HasDerivAt y y' t) (hy0 : y t ≠ 0)
    (hW : ∀ i, HasDerivAt (fun s => W s i) (W' i) t) :
    HasDerivAt (fun s => gaussianLog κ κ' v v' (y s) (W s))
      (-(d : ℝ) * (y' / y t) -
        ((y' / 2) * (κ * squaredDistance (W t) v + κ' * squaredDistance (W t) v') +
        y t / 2 *
          (κ * (∑ i, 2 * inner ℝ (W t i - (v i : ℂ)) (W' i)) +
           κ' * (∑ i, 2 * inner ℝ (W t i - (v' i : ℂ)) (W' i))))) t := by
  exact ((hy.log hy0).const_mul (-(d : ℝ))).sub
    ((hy.div_const 2).mul
      (((hasDerivAt_squaredDistance W W' v t hW).const_mul κ).add
        ((hasDerivAt_squaredDistance W W' v' t hW).const_mul κ')))

/-- Ordinary derivative of the exact Gaussian pair. -/
theorem hasDerivAt_gaussianPair {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (y : ℝ → ℝ) (y' : ℝ) (W : ℝ → Fin d → ℂ) (W' : Fin d → ℂ) (t : ℝ)
    (hy : HasDerivAt y y' t) (hy0 : y t ≠ 0)
    (hW : ∀ i, HasDerivAt (fun s => W s i) (W' i) t) :
    HasDerivAt (fun s => gaussianPair κ κ' v v' (y s) (W s))
      (gaussianPair κ κ' v v' (y t) (W t) *
       (-(d : ℝ) * (y' / y t) -
        ((y' / 2) * (κ * squaredDistance (W t) v + κ' * squaredDistance (W t) v') +
        y t / 2 *
          (κ * (∑ i, 2 * inner ℝ (W t i - (v i : ℂ)) (W' i)) +
           κ' * (∑ i, 2 * inner ℝ (W t i - (v' i : ℂ)) (W' i)))))) t := by
  exact (hasDerivAt_gaussianLog κ κ' v v' y y' W W' t hy hy0 hW).exp

/-- A real line in the actual complex imaginary-coordinate space. -/
def imaginaryLine {d : ℕ} (z h : Index d → ℂ) (t : ℝ) : Index d → ℂ :=
  fun a => z a + (t : ℂ) * h a

@[simp] theorem imaginaryLine_zero {d : ℕ} (z h : Index d → ℂ) :
    imaginaryLine z h 0 = z := by
  funext a
  simp [imaginaryLine]

theorem hasDerivAt_imaginaryLine {d : ℕ} (z h : Index d → ℂ) (a : Index d) :
    HasDerivAt (fun t : ℝ => imaginaryLine z h t a) (h a) 0 := by
  have hc : HasDerivAt (fun t : ℂ => z a + t * h a) (h a) (0 : ℂ) := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (h a)).const_add (z a)
  exact hc.comp_ofReal

private theorem hasDerivAt_complex_norm {f : ℝ → ℂ} {f' : ℂ} {t : ℝ}
    (hf : HasDerivAt f f' t) (h0 : f t ≠ 0) :
    HasDerivAt (fun s => ‖f s‖) (inner ℝ (f t) f' / ‖f t‖) t := by
  have hh := hf.norm_sq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr h0))
  convert hh using 1
  · funext s
    simp
  · simp
    ring

def radiusSlope {d : ℕ} (z h : Index d → ℂ) : ℝ :=
  inner ℝ (z none) (h none) / ‖z none‖

def ratioSlope {d : ℕ} (z h : Index d → ℂ) : Fin d → ℂ :=
  fun i => (h (some (some i)) * z none - z (some (some i)) * h none) / z none ^ 2

theorem hasDerivAt_radius_line {d : ℕ} (z h : Index d → ℂ) (hY : z none ≠ 0) :
    HasDerivAt (fun t => ‖imaginaryLine z h t none‖) (radiusSlope z h) 0 := by
  simpa [imaginaryLine, radiusSlope] using
    hasDerivAt_complex_norm (hasDerivAt_imaginaryLine z h none)
      (by simpa [imaginaryLine] using hY)

theorem hasDerivAt_ratio_line {d : ℕ} (z h : Index d → ℂ) (hY : z none ≠ 0)
    (i : Fin d) :
    HasDerivAt (fun t => ratio (imaginaryLine z h t) i) (ratioSlope z h i) 0 := by
  have hc (a : Index d) : HasDerivAt (fun t : ℂ => z a + t * h a) (h a) (0 : ℂ) := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (h a)).const_add (z a)
  have hh := ((hc (some (some i))).div (hc none) (by simpa using hY)).comp_ofReal
  simpa [ratio, imaginaryLine, ratioSlope] using hh

/-- The actual scalar field `N` on the imaginary coordinates. -/
def gaussianField {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ) (z : Index d → ℂ) : ℝ :=
  gaussianPair κ κ' v v' ‖z none‖ (ratio z)

/-- Explicit directional derivative of `log N` in the actual imaginary coordinates. -/
def gaussianLogSlope {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (z h : Index d → ℂ) : ℝ :=
  -(d : ℝ) * (radiusSlope z h / ‖z none‖) -
    ((radiusSlope z h / 2) *
      (κ * squaredDistance (ratio z) v + κ' * squaredDistance (ratio z) v') +
      ‖z none‖ / 2 *
        (κ * (∑ i, 2 * inner ℝ (ratio z i - (v i : ℂ)) (ratioSlope z h i)) +
         κ' * (∑ i, 2 * inner ℝ (ratio z i - (v' i : ℂ)) (ratioSlope z h i))))

/-- Every real directional derivative of the exact Gaussian field is verified. -/
theorem hasDerivAt_gaussianField_line {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (z h : Index d → ℂ) (hY : z none ≠ 0) :
    HasDerivAt (fun t => gaussianField κ κ' v v' (imaginaryLine z h t))
      (gaussianField κ κ' v v' z * gaussianLogSlope κ κ' v v' z h) 0 := by
  have hh := hasDerivAt_gaussianPair κ κ' v v'
    (fun t => ‖imaginaryLine z h t none‖) (radiusSlope z h)
    (fun t => ratio (imaginaryLine z h t)) (ratioSlope z h) 0
    (hasDerivAt_radius_line z h hY)
    (by simpa [imaginaryLine] using norm_ne_zero_iff.mpr hY)
    (hasDerivAt_ratio_line z h hY)
  simpa only [gaussianField, gaussianLogSlope, imaginaryLine_zero] using hh

/-- The two real directional derivatives that form `∑ conj(Vₐ) barDₐ`.
The equivalence with the coordinate sum is real linearity of the differential. -/
def barDirectional {d : ℕ} (f : (Index d → ℂ) → ℝ) (z V : Index d → ℂ) : ℂ :=
  ((deriv (fun t => f (imaginaryLine z V t)) 0 : ℝ) : ℂ) +
    Complex.I * ((deriv (fun t => f (imaginaryLine z (fun a => Complex.I * V a) t)) 0 : ℝ) : ℂ)

theorem gaussianField_barDirectional {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (z V : Index d → ℂ) (hY : z none ≠ 0) :
    barDirectional (gaussianField κ κ' v v') z V =
      (gaussianField κ κ' v v' z : ℂ) *
        ((gaussianLogSlope κ κ' v v' z V : ℂ) +
          Complex.I * (gaussianLogSlope κ κ' v v' z (fun a => Complex.I * V a) : ℂ)) := by
  unfold barDirectional
  rw [(hasDerivAt_gaussianField_line κ κ' v v' z V hY).deriv,
    (hasDerivAt_gaussianField_line κ κ' v v' z (fun a => Complex.I * V a) hY).deriv]
  push_cast
  ring

theorem complex_inner_pair (a b : ℂ) :
    (inner ℝ a b : ℂ) + Complex.I * (inner ℝ a (Complex.I * b) : ℂ) = a * star b := by
  apply Complex.ext <;> simp <;> ring

def distanceSlope {d : ℕ} (W h : Fin d → ℂ) (v : Fin d → ℝ) : ℝ :=
  ∑ i, 2 * inner ℝ (W i - (v i : ℂ)) (h i)

theorem distanceSlope_pair {d : ℕ} (W h : Fin d → ℂ) (v : Fin d → ℝ) :
    (distanceSlope W h v : ℂ) +
      Complex.I * (distanceSlope W (fun i => Complex.I * h i) v : ℂ) =
    2 * ∑ i, (W i - (v i : ℂ)) * star (h i) := by
  simp only [distanceSlope, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  linear_combination (2 : ℂ) * complex_inner_pair (W i - (v i : ℂ)) (h i)

def energySlope {d : ℕ} (y : ℝ) (W : Fin d → ℂ) (y' : ℝ)
    (W' : Fin d → ℂ) (v : Fin d → ℝ) : ℝ :=
  y' * squaredDistance W v + y * distanceSlope W W' v

theorem energySlope_pair {d : ℕ} (y y₁ y₂ : ℝ) (W h : Fin d → ℂ) (v : Fin d → ℝ) :
    (energySlope y W y₁ h v : ℂ) +
      Complex.I * (energySlope y W y₂ (fun i => Complex.I * h i) v : ℂ) =
    ((y₁ : ℂ) + Complex.I * (y₂ : ℂ)) * (squaredDistance W v : ℂ) +
      (y : ℂ) * (2 * ∑ i, (W i - (v i : ℂ)) * star (h i)) := by
  have hd := distanceSlope_pair W h v
  simp only [energySlope, Complex.ofReal_add, Complex.ofReal_mul]
  linear_combination (y : ℂ) * hd

theorem ratioSlope_I {d : ℕ} (z h : Index d → ℂ) (i : Fin d) :
    ratioSlope z (fun a => Complex.I * h a) i = Complex.I * ratioSlope z h i := by
  unfold ratioSlope
  ring

theorem radiusSlope_pair {d : ℕ} (z h : Index d → ℂ) :
    (radiusSlope z h : ℂ) +
      Complex.I * (radiusSlope z (fun a => Complex.I * h a) : ℂ) =
        z none * star (h none) / (‖z none‖ : ℂ) := by
  unfold radiusSlope
  push_cast
  rw [← mul_div_assoc, ← add_div, complex_inner_pair]

theorem ratioSlope_tangentVector {d : ℕ} (z : Index d → ℂ) (hY : z none ≠ 0)
    (v : Fin d → ℝ) (i : Fin d) :
    ratioSlope z (tangentVector (fun i => (v i : ℂ)) (ratio z)) i =
      ((v i : ℂ) - ratio z i) / (2 * z none) := by
  simp only [ratioSlope, tangentVector, ratio]
  field_simp
  ring

theorem radiusSlope_tangentVector_pair {d : ℕ} (z : Index d → ℂ)
    (v : Fin d → ℝ) :
    (radiusSlope z (tangentVector (fun i => (v i : ℂ)) (ratio z)) : ℂ) +
      Complex.I * (radiusSlope z
        (fun a => Complex.I * tangentVector (fun i => (v i : ℂ)) (ratio z) a) : ℂ) =
      z none / (‖z none‖ : ℂ) := by
  rw [radiusSlope_pair]
  simp [tangentVector]

theorem norm_square_eq_mul_star (z : ℂ) : (‖z‖ : ℂ) ^ 2 = z * star z := by
  rw [← Complex.ofReal_pow]
  apply Complex.ext <;> simp [Complex.sq_norm, Complex.normSq_apply] ; ring

theorem norm_div_star (Y : ℂ) (hY : Y ≠ 0) :
    (‖Y‖ : ℂ) / star Y = Y / (‖Y‖ : ℂ) := by
  have hn : (‖Y‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hY
  have hs : star Y ≠ 0 := star_ne_zero.mpr hY
  apply (div_eq_div_iff hs hn).mpr
  simpa only [← pow_two] using norm_square_eq_mul_star Y

theorem squaredDistance_coe {d : ℕ} (W : Fin d → ℂ) (v : Fin d → ℝ) :
    (squaredDistance W v : ℂ) =
      ∑ i, (W i - (v i : ℂ)) * star (W i - (v i : ℂ)) := by
  simp only [squaredDistance, Complex.ofReal_sum, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro i _
  exact norm_square_eq_mul_star _

private theorem gaussian_energy_cancellation {d : ℕ} (Y : ℂ) (hY : Y ≠ 0)
    (W : Fin d → ℂ) (v w : Fin d → ℝ) :
    (Y / (‖Y‖ : ℂ)) * (squaredDistance W w : ℂ) +
      (‖Y‖ : ℂ) * (2 * ∑ i, (W i - (w i : ℂ)) *
        star (((v i : ℂ) - W i) / (2 * Y))) =
    (Y / (‖Y‖ : ℂ)) * ∑ i, (W i - (w i : ℂ)) * ((v i : ℂ) - (w i : ℂ)) := by
  rw [squaredDistance_coe]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hs : star Y ≠ 0 := star_ne_zero.mpr hY
  have hc : (‖Y‖ : ℂ) * (2 * ((W i - (w i : ℂ)) *
      star (((v i : ℂ) - W i) / (2 * Y)))) =
      ((‖Y‖ : ℂ) / star Y) * (W i - (w i : ℂ)) * ((v i : ℂ) - star (W i)) := by
    simp only [star_div₀, star_sub, star_mul, star_ofNat, Complex.star_def,
      Complex.conj_ofReal]
    field_simp
  rw [hc, norm_div_star Y hY]
  simp only [star_sub, Complex.star_def, Complex.conj_ofReal]
  ring

/-- The Gaussian directional cancellation in equation (gaussian-directional-identity),
written using the two actual real differential components already proved above. -/
theorem gaussian_energy_tangent_pair {d : ℕ} (z : Index d → ℂ) (hY : z none ≠ 0)
    (v w : Fin d → ℝ) :
    let V := tangentVector (fun i => (v i : ℂ)) (ratio z)
    (energySlope ‖z none‖ (ratio z) (radiusSlope z V) (ratioSlope z V) w : ℂ) +
      Complex.I * (energySlope ‖z none‖ (ratio z)
        (radiusSlope z (fun a => Complex.I * V a))
        (ratioSlope z (fun a => Complex.I * V a)) w : ℂ) =
      (z none / (‖z none‖ : ℂ)) *
        ∑ i, (ratio z i - (w i : ℂ)) * ((v i : ℂ) - (w i : ℂ)) := by
  dsimp only
  rw [funext (ratioSlope_I z (tangentVector (fun i => (v i : ℂ)) (ratio z)))]
  rw [energySlope_pair, radiusSlope_tangentVector_pair]
  simp_rw [ratioSlope_tangentVector z hY]
  exact gaussian_energy_cancellation (z none) hY (ratio z) v w

theorem gaussianLogSlope_energy {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (z h : Index d → ℂ) :
    gaussianLogSlope κ κ' v v' z h =
      -(d : ℝ) * (radiusSlope z h / ‖z none‖) -
      (κ * energySlope ‖z none‖ (ratio z) (radiusSlope z h) (ratioSlope z h) v +
       κ' * energySlope ‖z none‖ (ratio z) (radiusSlope z h) (ratioSlope z h) v') / 2 := by
  unfold gaussianLogSlope energySlope distanceSlope
  ring

theorem gaussian_energy_tangent_pair_phase {d : ℕ} (z : Index d → ℂ)
    (hY : z none ≠ 0) (v w : Fin d → ℝ) :
    let V := tangentVector (fun i => (v i : ℂ)) (ratio z)
    (energySlope ‖z none‖ (ratio z) (radiusSlope z V) (ratioSlope z V) w : ℂ) +
      Complex.I * (energySlope ‖z none‖ (ratio z)
        (radiusSlope z (fun a => Complex.I * V a))
        (ratioSlope z (fun a => Complex.I * V a)) w : ℂ) =
      -2 * (z none / (‖z none‖ : ℂ)) *
        (∑ a, phaseRow (fun i => (w i : ℂ)) a * V a) := by
  dsimp only
  rw [gaussian_energy_tangent_pair z hY, phase_polarization]
  have hs : (∑ i, ((w i : ℂ) - ratio z i) * ((w i : ℂ) - (v i : ℂ))) =
      ∑ i, (ratio z i - (w i : ℂ)) * ((v i : ℂ) - (w i : ℂ)) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

/-- The full logarithmic Gaussian directional identity, for two distinct modes. -/
theorem gaussianLogSlope_tangent_pair {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (z : Index d → ℂ) (hY : z none ≠ 0) :
    let V := tangentVector (fun i => (v i : ℂ)) (ratio z)
    (gaussianLogSlope κ κ' v v' z V : ℂ) +
      Complex.I * (gaussianLogSlope κ κ' v v' z (fun a => Complex.I * V a) : ℂ) =
      (z none / (‖z none‖ : ℂ)) *
        (-(d : ℂ) / (‖z none‖ : ℂ) +
          (κ' : ℂ) * ∑ a, phaseRow (fun i => (v' i : ℂ)) a * V a) := by
  dsimp only
  have hr := radiusSlope_tangentVector_pair z v
  have hv := gaussian_energy_tangent_pair_phase z hY v v
  have hv' := gaussian_energy_tangent_pair_phase z hY v v'
  dsimp only at hv hv'
  rw [phase_tangent] at hv
  simp only [mul_zero] at hv
  simp only [gaussianLogSlope_energy, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_neg, Complex.ofReal_natCast, Complex.ofReal_div,
    Complex.ofReal_add, Complex.ofReal_ofNat]
  linear_combination (-(d : ℂ) / (‖z none‖ : ℂ)) * hr -
    ((κ : ℂ) / 2) * hv - ((κ' : ℂ) / 2) * hv'

/-- Equation (current-log-derivative) applied to the exact scalar Gaussian field. -/
theorem gaussianField_tangent_derivative {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (z : Index d → ℂ) (hY : z none ≠ 0) :
    let V := tangentVector (fun i => (v i : ℂ)) (ratio z)
    barDirectional (gaussianField κ κ' v v') z V =
      (gaussianField κ κ' v v' z : ℂ) * (z none / (‖z none‖ : ℂ)) *
        (-(d : ℂ) / (‖z none‖ : ℂ) +
          (κ' : ℂ) * ∑ a, phaseRow (fun i => (v' i : ℂ)) a * V a) := by
  dsimp only
  rw [gaussianField_barDirectional κ κ' v v' z _ hY,
    gaussianLogSlope_tangent_pair κ κ' v v' z hY]
  ring

end
end OAI.Analysis.Calculus.Current
