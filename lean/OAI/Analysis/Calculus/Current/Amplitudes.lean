import OAI.Analysis.Calculus.Current.Superposition

namespace OAI.Analysis.Calculus.Current

noncomputable section

def movingEmbed (e c : ℂ) : Quaternion ℝ :=
  (c.re : Quaternion ℝ) + (complexK e * qi) * (c.im : Quaternion ℝ)

theorem movingEmbed_star (e c : ℂ) : star (movingEmbed e c) = movingEmbed e (star c) := by
  ext <;> simp [movingEmbed, complexK, qi] <;> ring

theorem movingEmbed_multiply (e : ℂ) (he : Complex.normSq e = 1) (c d : ℂ) :
    movingEmbed e c * movingEmbed e d = movingEmbed e (c * d) :=
  movingEmbedding_mul e he c d

theorem movingUnit_normSq {d : ℕ} (z : Index d → ℂ) (hY : z none ≠ 0) :
    Complex.normSq (movingUnit z) = 1 := by
  have hh := congrArg Complex.re (movingUnit_mul_star z hY)
  simpa [Complex.normSq_apply, Complex.mul_re, Complex.star_def] using hh

def modeCovector {d : ℕ} (κ : ℝ) (v : Fin d → ℝ) (a : Index d) : ℝ :=
  κ * realPhaseRow v a

def phaseComplex {d : ℕ} (cR cI : ℝ) (L x : Index d → ℝ) : ℂ :=
  ⟨phaseF cR cI L x, phaseG cR cI L x⟩

def crossReal (cR cI dR dI : ℝ) : ℝ := cR * dR + cI * dI
def crossImag (cR cI dR dI : ℝ) : ℝ := cR * dI - cI * dR

theorem phaseArgument_difference {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (x : Index d → ℝ) :
    phaseArgument (phaseDifference κ κ' v v') x =
      phaseArgument (modeCovector κ' v') x - phaseArgument (modeCovector κ v) x := by
  simp [phaseArgument, phaseDifference, modeCovector, sub_mul, Finset.sum_sub_distrib]

theorem phaseComplex_cross {d : ℕ} (κ κ' cR cI dR dI : ℝ)
    (v v' : Fin d → ℝ) (x : Index d → ℝ) :
    star (phaseComplex cR cI (modeCovector κ v) x) *
        phaseComplex dR dI (modeCovector κ' v') x =
      phaseComplex (crossReal cR cI dR dI) (crossImag cR cI dR dI)
        (phaseDifference κ κ' v v') x := by
  apply Complex.ext <;> simp only [phaseComplex, phaseF, phaseG, crossReal, crossImag,
    Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, phaseArgument_difference, Real.cos_sub, Real.sin_sub] <;> ring

def modeEnvelope {d : ℕ} (κ : ℝ) (v : Fin d → ℝ) (z : Index d → ℂ) : ℝ :=
  Real.exp (-(d : ℝ) / 2 * Real.log ‖z none‖ -
    κ * ‖z none‖ / 2 * squaredDistance (ratio z) v)

theorem modeEnvelope_product {d : ℕ} (κ κ' : ℝ) (v v' : Fin d → ℝ)
    (z : Index d → ℂ) :
    modeEnvelope κ v z * modeEnvelope κ' v' z = gaussianField κ κ' v v' z := by
  unfold modeEnvelope gaussianField gaussianPair gaussianLog
  rw [← Real.exp_add]
  congr 1
  ring

/-- A single mode amplitude, with the constant frequency normalization absorbed
into `cR,cI`. `normalizedModeAmplitude` below restores it explicitly. -/
def modeAmplitude {d : ℕ} (κ cR cI : ℝ) (v : Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) : Quaternion ℝ :=
  movingEmbed (movingUnit z)
    ((modeEnvelope κ v z : ℂ) * phaseComplex cR cI (modeCovector κ v) x)

theorem complex_amplitude_cross {d : ℕ} (κ κ' cR cI dR dI : ℝ)
    (v v' : Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ) :
    star ((modeEnvelope κ v z : ℂ) * phaseComplex cR cI (modeCovector κ v) x) *
        ((modeEnvelope κ' v' z : ℂ) * phaseComplex dR dI (modeCovector κ' v') x) =
      (gaussianField κ κ' v v' z : ℂ) *
        phaseComplex (crossReal cR cI dR dI) (crossImag cR cI dR dI)
          (phaseDifference κ κ' v v') x := by
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  rw [← modeEnvelope_product κ κ' v v' z, Complex.ofReal_mul,
    ← phaseComplex_cross κ κ' cR cI dR dI v v' x]
  simp only [Complex.star_def]
  ring

theorem modeAmplitude_cross {d : ℕ} (κ κ' cR cI dR dI : ℝ)
    (v v' : Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0) :
    star (modeAmplitude κ cR cI v x z) * modeAmplitude κ' dR dI v' x z =
      ((gaussianField κ κ' v v' z *
        phaseF (crossReal cR cI dR dI) (crossImag cR cI dR dI)
          (phaseDifference κ κ' v v') x : ℝ) : Quaternion ℝ) +
      ((gaussianField κ κ' v v' z *
        phaseG (crossReal cR cI dR dI) (crossImag cR cI dR dI)
          (phaseDifference κ κ' v v') x : ℝ) : Quaternion ℝ) * complexK (movingUnit z) * qi := by
  unfold modeAmplitude
  rw [movingEmbed_star, movingEmbed_multiply _ (movingUnit_normSq z hY),
    complex_amplitude_cross]
  ext <;> simp [movingEmbed, phaseComplex, complexK, qi] <;> ring

end
end OAI.Analysis.Calculus.Current
