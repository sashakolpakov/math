import OAI.RepresentationTheory.Weil.Local.OscillatoryTailTools
import OAI.RepresentationTheory.Weil.Local.ArchimedeanTestSpace

/-! # Planar Quadratic Phase -/

namespace OAI.RepresentationTheory.Weil.Local.PlanarQuadraticPhase.Construction

noncomputable section

/-! The planar quadratic phase satisfies a radial Laplacian identity. -/

def planarQuadraticPhase (b : ℝ) (z : ℝ × ℝ) : ℂ :=
  Complex.exp ((b : ℂ) * Complex.I * ((z.1 : ℂ) ^ 2 - (z.2 : ℂ) ^ 2))

def planarQuadraticPhaseX (b : ℝ) (z : ℝ × ℝ) : ℂ :=
  (2 * b * Complex.I * z.1 : ℂ) * planarQuadraticPhase b z

def planarQuadraticPhaseY (b : ℝ) (z : ℝ × ℝ) : ℂ :=
  (-2 * b * Complex.I * z.2 : ℂ) * planarQuadraticPhase b z

def planarQuadraticPhaseXX (b : ℝ) (z : ℝ × ℝ) : ℂ :=
  ((2 * b * Complex.I : ℂ) + (2 * b * Complex.I * z.1 : ℂ) ^ 2) * planarQuadraticPhase b z

def planarQuadraticPhaseYY (b : ℝ) (z : ℝ × ℝ) : ℂ :=
  ((-2 * b * Complex.I : ℂ) + (-2 * b * Complex.I * z.2 : ℂ) ^ 2) * planarQuadraticPhase b z

theorem planarQuadraticPhase_norm (b : ℝ) (z : ℝ × ℝ) : ‖planarQuadraticPhase b z‖ = 1 := by
  simp [planarQuadraticPhase, Complex.norm_exp, pow_two]

theorem planarQuadraticPhase_continuous (b : ℝ) : Continuous (planarQuadraticPhase b) := by
  unfold planarQuadraticPhase
  fun_prop

theorem planarQuadraticPhase_hasDerivAt_x (b x y : ℝ) :
    HasDerivAt (fun t => planarQuadraticPhase b (t, y)) (planarQuadraticPhaseX b (x, y)) x := by
  have hd := (((((hasDerivAt_id x).ofReal_comp).pow 2).sub_const ((y : ℂ) ^ 2)).const_mul
    ((b : ℂ) * Complex.I)).cexp
  dsimp only [id_eq, Pi.pow_apply] at hd
  convert! hd using 1
  unfold planarQuadraticPhaseX planarQuadraticPhase
  norm_num
  ring

theorem planarQuadraticPhase_hasDerivAt_y (b x y : ℝ) :
    HasDerivAt (fun t => planarQuadraticPhase b (x, t)) (planarQuadraticPhaseY b (x, y)) y := by
  have hd := (((((hasDerivAt_id y).ofReal_comp).pow 2).const_sub ((x : ℂ) ^ 2)).const_mul
    ((b : ℂ) * Complex.I)).cexp
  dsimp only [id_eq, Pi.pow_apply] at hd
  convert! hd using 1
  unfold planarQuadraticPhaseY planarQuadraticPhase
  norm_num
  ring

theorem planarQuadraticPhaseX_hasDerivAt_x (b x y : ℝ) :
    HasDerivAt (fun t => planarQuadraticPhaseX b (t, y)) (planarQuadraticPhaseXX b (x, y)) x := by
  have hd := (((hasDerivAt_id x).ofReal_comp).const_mul (2 * b * Complex.I : ℂ)).mul
    (planarQuadraticPhase_hasDerivAt_x b x y)
  dsimp only [id_eq] at hd
  convert! hd using 1
  unfold planarQuadraticPhaseXX planarQuadraticPhaseX
  norm_num
  ring

theorem planarQuadraticPhaseY_hasDerivAt_y (b x y : ℝ) :
    HasDerivAt (fun t => planarQuadraticPhaseY b (x, t)) (planarQuadraticPhaseYY b (x, y)) y := by
  have hd := (((hasDerivAt_id y).ofReal_comp).const_mul (-2 * b * Complex.I : ℂ)).mul
    (planarQuadraticPhase_hasDerivAt_y b x y)
  dsimp only [id_eq] at hd
  convert! hd using 1
  unfold planarQuadraticPhaseYY planarQuadraticPhaseY
  norm_num
  ring

theorem planarQuadraticPhase_laplacian (b : ℝ) (z : ℝ × ℝ) :
    planarQuadraticPhaseXX b z + planarQuadraticPhaseYY b z =
      (-4 * b ^ 2 * (z.1 ^ 2 + z.2 ^ 2) : ℝ) * planarQuadraticPhase b z := by
  unfold planarQuadraticPhaseXX planarQuadraticPhaseYY
  rw [← add_mul]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem planarQuadraticPhase_standard (z : ℂ) :
    planarQuadraticPhase Real.pi (z.re, z.im) = ArchimedeanTestSpace.Construction.complexStandardCharacter (z ^ 2 / 2) := by
  change Complex.exp _ = Gaussian.Construction.realCharacter 1 ((z ^ 2 / 2).re)
  rw [Gaussian.Construction.realCharacter_apply]
  congr 1
  simp only [Complex.div_ofNat_re, pow_two, Complex.mul_re]
  push_cast
  ring

end

end OAI.RepresentationTheory.Weil.Local.PlanarQuadraticPhase.Construction
