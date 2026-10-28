import OAI.Analysis.Calculus.Current.Wave

namespace OAI.Analysis.Calculus.Current

noncomputable section

def realQCLM : ℝ →L[ℝ] Quaternion ℝ := (ContinuousLinearMap.id ℝ ℝ).smulRight 1

def complexKCLM : ℂ →L[ℝ] Quaternion ℝ :=
  Complex.reCLM.smulRight 1 + Complex.imCLM.smulRight (complexK Complex.I)

theorem realQCLM_apply (r : ℝ) : realQCLM r = (r : Quaternion ℝ) := by
  ext <;> simp [realQCLM]

theorem complexKCLM_apply (c : ℂ) : complexKCLM c = complexK c := by
  ext <;> simp [complexKCLM, complexK]

theorem contDiff_complexK : ContDiff ℝ ⊤ (fun c : ℂ => complexK c) := by
  have heq : (fun c : ℂ => complexK c) = complexKCLM :=
    funext (fun c => (complexKCLM_apply c).symm)
  rw [heq]
  exact complexKCLM.contDiff

def quaternionReCLM : Quaternion ℝ →L[ℝ] ℝ :=
  { QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1) with cont := Quaternion.continuous_re }

theorem contDiff_starQ : ContDiff ℝ ⊤ (star : Quaternion ℝ → Quaternion ℝ) := by
  have hr : ContDiff ℝ ⊤ (fun q : Quaternion ℝ => (q.re : Quaternion ℝ)) := by
    convert realQCLM.contDiff.comp quaternionReCLM.contDiff using 1
    funext q
    exact (realQCLM_apply _).symm
  convert (hr.add hr).sub contDiff_id using 1
  funext q
  ext <;> simp

theorem contDiff_movingEmbed :
    ContDiff ℝ ⊤ (fun p : ℂ × ℂ => movingEmbed p.1 p.2) := by
  have he : ContDiff ℝ ⊤ (fun p : ℂ × ℂ => complexK p.1) :=
    contDiff_complexK.comp contDiff_fst
  have hr : ContDiff ℝ ⊤ (fun p : ℂ × ℂ => (p.2.re : Quaternion ℝ)) := by
    have hp : ContDiff ℝ ⊤ (fun p : ℂ × ℂ => p.2.re) :=
      Complex.reCLM.contDiff.comp (contDiff_snd : ContDiff ℝ ⊤ (Prod.snd : ℂ × ℂ → ℂ))
    convert realQCLM.contDiff.comp hp using 1
    funext p
    exact (realQCLM_apply _).symm
  have hi : ContDiff ℝ ⊤ (fun p : ℂ × ℂ => (p.2.im : Quaternion ℝ)) := by
    have hp : ContDiff ℝ ⊤ (fun p : ℂ × ℂ => p.2.im) :=
      Complex.imCLM.contDiff.comp (contDiff_snd : ContDiff ℝ ⊤ (Prod.snd : ℂ × ℂ → ℂ))
    convert realQCLM.contDiff.comp hp using 1
    funext p
    exact (realQCLM_apply _).symm
  exact hr.add ((he.mul contDiff_const).mul hi)

theorem contDiffAt_ratio {d : ℕ} (z : Index d → ℂ) (hY : z none ≠ 0) (i : Fin d) :
    ContDiffAt ℝ ⊤ (fun w => ratio w i) z := by
  unfold ratio
  simp only [div_eq_mul_inv]
  fun_prop (disch := assumption)

theorem contDiffAt_movingUnit {d : ℕ} (z : Index d → ℂ) (hY : z none ≠ 0) :
    ContDiffAt ℝ ⊤ (movingUnit (d := d)) z := by
  have hy : ContDiffAt ℝ ⊤ (fun w : Index d → ℂ => ‖w none‖) z :=
    (contDiffAt_apply ℝ ℂ none z).norm ℂ hY
  have hC : ContDiffAt ℝ ⊤ (fun w : Index d → ℂ => (‖w none‖ : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z hy
  have hn : (‖z none‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hY
  change ContDiffAt ℝ ⊤ (fun w : Index d → ℂ => w none / (‖w none‖ : ℂ)) z
  simpa only [div_eq_mul_inv] using
    (contDiffAt_apply ℝ ℂ none z).mul (hC.fun_inv hn)

theorem contDiffAt_modeEnvelope {d : ℕ} (κ : ℝ) (v : Fin d → ℝ)
    (z : Index d → ℂ) (hY : z none ≠ 0) :
    ContDiffAt ℝ ⊤ (modeEnvelope κ v) z := by
  have hy : ContDiffAt ℝ ⊤ (fun w : Index d → ℂ => ‖w none‖) z :=
    (contDiffAt_apply ℝ ℂ none z).norm ℂ hY
  have hn : ‖z none‖ ≠ 0 := norm_ne_zero_iff.mpr hY
  have hd : ContDiffAt ℝ ⊤ (fun w => squaredDistance (ratio w) v) z := by
    apply ContDiffAt.sum
    intro i _
    exact ((contDiffAt_ratio z hY i).sub contDiffAt_const).norm_sq ℂ
  unfold modeEnvelope
  fun_prop (disch := assumption)

theorem contDiff_phaseComplex {d : ℕ} (cR cI : ℝ) (L : Index d → ℝ) :
    ContDiff ℝ ⊤ (phaseComplex cR cI L) := by
  have hF : ContDiff ℝ ⊤ (phaseF cR cI L) := by unfold phaseF phaseArgument; fun_prop
  have hG : ContDiff ℝ ⊤ (phaseG cR cI L) := by unfold phaseG phaseArgument; fun_prop
  have heq : phaseComplex cR cI L =
      (fun x => (phaseF cR cI L x : ℂ) + Complex.I * (phaseG cR cI L x : ℂ)) := by
    funext x
    apply Complex.ext <;> simp [phaseComplex]
  rw [heq]
  exact (Complex.ofRealCLM.contDiff.comp hF).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hG))

theorem contDiffAt_modeAmplitude {d : ℕ} (κ cR cI : ℝ) (v : Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0) :
    ContDiffAt ℝ ⊤ (fun p : (Index d → ℝ) × (Index d → ℂ) => modeAmplitude κ cR cI v p.1 p.2)
      (x, z) := by
  have he := (contDiffAt_movingUnit z hY).comp (x, z) contDiffAt_snd
  have hn := (contDiffAt_modeEnvelope κ v z hY).comp (x, z) contDiffAt_snd
  have hp := (contDiff_phaseComplex cR cI (modeCovector κ v)).contDiffAt.comp (x, z) contDiffAt_fst
  have hnc := Complex.ofRealCLM.contDiff.contDiffAt.comp (x, z) hn
  exact contDiff_movingEmbed.contDiffAt.comp (x, z) (he.prodMk (hnc.mul hp))

theorem contDiffAt_tangentField {d : ℕ} (v : Fin d → ℝ)
    (z : Index d → ℂ) (hY : z none ≠ 0) (a : Index d) :
    ContDiffAt ℝ ⊤ (fun w => tangentField v w a) z := by
  have hr := contDiffAt_ratio z hY
  cases a with
  | none => exact contDiffAt_const
  | some a =>
    cases a with
    | none =>
      change ContDiffAt ℝ ⊤ (fun w => -(∑ i, ratio w i * (v i : ℂ)) / 2) z
      fun_prop
    | some i =>
      change ContDiffAt ℝ ⊤ (fun w => ((v i : ℂ) + ratio w i) / 2) z
      fun_prop

/-- Joint smoothness in all real and imaginary coordinates on `Y ≠ 0`. -/
theorem contDiffAt_modeCurrent {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) (a b : Index d) :
    ContDiffAt ℝ ⊤ (fun p : (Index d → ℝ) × (Index d → ℂ) => modeCurrent κ cR cI v p.1 p.2 a b)
      (x, z) := by
  have hχ (a : Index d) : ContDiffAt ℝ ⊤
      (fun p : (Index d → ℝ) × (Index d → ℂ) =>
        currentColumn (ratio p.2) (fun j i => (v j i : ℂ))
          (fun j => modeAmplitude (κ j) (cR j) (cI j) (v j) p.1 p.2) a) (x, z) := by
    apply ContDiffAt.sum
    intro j _
    have hV := (contDiffAt_tangentField (v j) z hY a).comp (x, z) contDiffAt_snd
    exact (contDiff_complexK.contDiffAt.comp (x, z) hV).mul
      (contDiff_starQ.contDiffAt.comp (x, z)
        (contDiffAt_modeAmplitude (κ j) (cR j) (cI j) (v j) x z hY))
  exact (hχ a).mul (contDiff_starQ.contDiffAt.comp (x, z) (hχ b))

theorem contDiffAt_waveCurrent {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) (a b : Index d) :
    ContDiffAt ℝ ⊤ (fun p : (Index d → ℝ) × (Index d → ℂ) => waveCurrent κ cR cI v p.1 p.2 a b)
      (x, z) :=
  contDiffAt_modeCurrent κ
    (fun j => frequencyNormalization d (κ j) * cR j)
    (fun j => frequencyNormalization d (κ j) * cI j) v x z hY a b

end
end OAI.Analysis.Calculus.Current
