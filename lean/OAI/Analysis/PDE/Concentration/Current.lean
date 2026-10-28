import OAI.Analysis.Calculus.Current.AmplitudeBounds
import OAI.Analysis.Calculus.Current.Regularized

namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current

noncomputable def movingEmbedAddHom (e : ℂ) : ℂ →+ Quaternion ℝ where
  toFun := OAI.Analysis.Calculus.Current.movingEmbed e
  map_zero' := by ext <;> simp [OAI.Analysis.Calculus.Current.movingEmbed, OAI.Analysis.Calculus.Current.complexK, OAI.Analysis.Calculus.Current.qi]
  map_add' c d := by ext <;> simp [OAI.Analysis.Calculus.Current.movingEmbed, OAI.Analysis.Calculus.Current.complexK, OAI.Analysis.Calculus.Current.qi] <;> ring

theorem movingEmbed_sum {ι : Type*} (e : ℂ) (s : Finset ι) (c : ι → ℂ) :
    OAI.Analysis.Calculus.Current.movingEmbed e (∑ j ∈ s, c j) = ∑ j ∈ s, OAI.Analysis.Calculus.Current.movingEmbed e (c j) :=
  map_sum (movingEmbedAddHom e) c s

theorem complexK_mul_movingEmbed (e w c : ℂ) :
    OAI.Analysis.Calculus.Current.complexK w * OAI.Analysis.Calculus.Current.movingEmbed e c =
      OAI.Analysis.Calculus.Current.movingEmbed e ((w.re : ℂ) * c) +
        OAI.Analysis.Calculus.Current.complexK Complex.I * OAI.Analysis.Calculus.Current.movingEmbed e ((w.im : ℂ) * c) := by
  ext <;> simp [OAI.Analysis.Calculus.Current.movingEmbed, OAI.Analysis.Calculus.Current.complexK, OAI.Analysis.Calculus.Current.qi] <;> ring

theorem moving_planes_norm_sq (e c d : ℂ) (he : Complex.normSq e = 1) :
    ‖OAI.Analysis.Calculus.Current.movingEmbed e c + OAI.Analysis.Calculus.Current.complexK Complex.I * OAI.Analysis.Calculus.Current.movingEmbed e d‖ ^ 2 = ‖c‖ ^ 2 + ‖d‖ ^ 2 := by
  have hs : Quaternion.normSq (OAI.Analysis.Calculus.Current.movingEmbed e c + OAI.Analysis.Calculus.Current.complexK Complex.I * OAI.Analysis.Calculus.Current.movingEmbed e d) =
      Complex.normSq c + Complex.normSq d := by
    simp only [Complex.normSq_apply] at he
    simp [Quaternion.normSq_def', OAI.Analysis.Calculus.Current.movingEmbed, OAI.Analysis.Calculus.Current.complexK, OAI.Analysis.Calculus.Current.qi, Complex.normSq_apply]
    nlinarith [congrArg (fun t : ℝ => t * c.im ^ 2) he,
      congrArg (fun t : ℝ => t * d.im ^ 2) he]
  simpa only [Quaternion.normSq_eq_norm_mul_self, Complex.normSq_eq_norm_sq, ← pow_two] using hs

/-- Real and imaginary scalar multipliers give two orthogonal complex planes
in the actual quaternionic current, including all cross-mode terms. -/
theorem finite_current_complex_decomposition {ι : Type*} [Fintype ι]
    (e : ℂ) (w c : ι → ℂ) :
    (∑ j, OAI.Analysis.Calculus.Current.complexK (w j) * star (OAI.Analysis.Calculus.Current.movingEmbed e (c j))) =
      OAI.Analysis.Calculus.Current.movingEmbed e (star (∑ j, ((w j).re : ℂ) * c j)) +
        OAI.Analysis.Calculus.Current.complexK Complex.I * OAI.Analysis.Calculus.Current.movingEmbed e (star (∑ j, ((w j).im : ℂ) * c j)) := by
  simp only [map_sum, map_mul, Complex.star_def, Complex.conj_ofReal, OAI.Analysis.Calculus.Current.movingEmbed_star,
    movingEmbed_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact complexK_mul_movingEmbed e (w j) (star (c j))

theorem finite_current_norm_sq {ι : Type*} [Fintype ι]
    (e : ℂ) (w c : ι → ℂ) (he : Complex.normSq e = 1) :
    ‖∑ j, OAI.Analysis.Calculus.Current.complexK (w j) * star (OAI.Analysis.Calculus.Current.movingEmbed e (c j))‖ ^ 2 =
      ‖∑ j, ((w j).re : ℂ) * c j‖ ^ 2 + ‖∑ j, ((w j).im : ℂ) * c j‖ ^ 2 := by
  rw [finite_current_complex_decomposition, moving_planes_norm_sq _ _ _ he]
  simp only [norm_star]

noncomputable def currentTimeFactor {d : ℕ} (W v : Fin d → ℂ) : ℂ :=
  (1 + (∑ i, W i * v i) / 2) / (Real.sqrt 2 : ℂ)

noncomputable def currentTimeColumn {d : ℕ} {ι : Type*} [Fintype ι]
    (W : Fin d → ℂ) (v : ι → Fin d → ℂ) (a : ι → Quaternion ℝ) : Quaternion ℝ :=
  (Real.sqrt 2)⁻¹ • (OAI.Analysis.Calculus.Current.currentColumn W v a none - OAI.Analysis.Calculus.Current.currentColumn W v a (some none))

theorem currentTimeColumn_eq_sum {d : ℕ} {ι : Type*} [Fintype ι]
    (W : Fin d → ℂ) (v : ι → Fin d → ℂ) (a : ι → Quaternion ℝ) :
    currentTimeColumn W v a = ∑ j, OAI.Analysis.Calculus.Current.complexK (currentTimeFactor W (v j)) * star (a j) := by
  unfold currentTimeColumn OAI.Analysis.Calculus.Current.currentColumn
  rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← sub_mul, ← smul_mul_assoc]
  congr 1
  have hi : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    field_simp
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ext <;> simp [currentTimeFactor, OAI.Analysis.Calculus.Current.tangentVector, OAI.Analysis.Calculus.Current.complexK, div_eq_mul_inv,
    Complex.inv_re, Complex.inv_im, Complex.normSq_ofReal, hi] <;> ring

noncomputable def currentModeScalar {d : ℕ} (κ cR cI : ℝ) (v : Fin d → ℝ)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) : ℂ :=
  (((κ / ‖z none‖) ^ ((d : ℝ) / 2) *
    Real.exp (-κ * ‖z none‖ / 2 * OAI.Analysis.Calculus.Current.squaredDistance (OAI.Analysis.Calculus.Current.ratio z) v) : ℝ) : ℂ) *
    OAI.Analysis.Calculus.Current.phaseComplex cR cI (OAI.Analysis.Calculus.Current.modeCovector κ v) x

/-- The current-column norm identity in the manuscript, for the fully
normalized wave amplitudes and the physical time direction. -/
theorem waveCurrentTime_norm_sq {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (hκ : ∀ j, 0 < κ j)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) (hY : z none ≠ 0) :
    ‖currentTimeColumn (OAI.Analysis.Calculus.Current.ratio z) (fun j i => (v j i : ℂ))
        (fun j => OAI.Analysis.Calculus.Current.normalizedModeAmplitude (κ j) (cR j) (cI j) (v j) x z)‖ ^ 2 =
      ‖∑ j, ((currentTimeFactor (OAI.Analysis.Calculus.Current.ratio z) (fun i => (v j i : ℂ))).re : ℂ) *
        currentModeScalar (κ j) (cR j) (cI j) (v j) x z‖ ^ 2 +
      ‖∑ j, ((currentTimeFactor (OAI.Analysis.Calculus.Current.ratio z) (fun i => (v j i : ℂ))).im : ℂ) *
        currentModeScalar (κ j) (cR j) (cI j) (v j) x z‖ ^ 2 := by
  rw [currentTimeColumn_eq_sum]
  simp_rw [OAI.Analysis.Calculus.Current.normalizedModeAmplitude_formula _ _ _ (hκ _) _ _ _ hY]
  exact finite_current_norm_sq _ _ _ (OAI.Analysis.Calculus.Current.movingUnit_normSq z hY)

theorem timeComponent_outer {d : ℕ} (u : OAI.Analysis.Calculus.Current.Index d → Quaternion ℝ) :
    OAI.Analysis.Calculus.Current.timeComponent (OAI.Analysis.Calculus.Quaternion.outer u) =
      ‖(Real.sqrt 2)⁻¹ • (u none - u (some none))‖ ^ 2 := by
  calc
    _ = Quaternion.normSq (u none - u (some none)) / 2 := by
      simp [OAI.Analysis.Calculus.Current.timeComponent, OAI.Analysis.Calculus.Quaternion.outer, Quaternion.normSq_def']
      ring
    _ = ‖u none - u (some none)‖ ^ 2 / 2 := by
      rw [Quaternion.normSq_eq_norm_mul_self]
      ring
    _ = _ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow,
        inv_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      ring

/-- The density's unsmoothed time component is exactly the sum of the two
scalar multiplier squares, with the manuscript's `1/√2` normalization. -/
theorem waveCurrent_timeComponent_eq {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (hκ : ∀ j, 0 < κ j)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) (hY : z none ≠ 0) :
    OAI.Analysis.Calculus.Current.timeComponent (OAI.Analysis.Calculus.Current.waveCurrent κ cR cI v x z) =
      ‖∑ j, ((currentTimeFactor (OAI.Analysis.Calculus.Current.ratio z) (fun i => (v j i : ℂ))).re : ℂ) *
        currentModeScalar (κ j) (cR j) (cI j) (v j) x z‖ ^ 2 +
      ‖∑ j, ((currentTimeFactor (OAI.Analysis.Calculus.Current.ratio z) (fun i => (v j i : ℂ))).im : ℂ) *
        currentModeScalar (κ j) (cR j) (cI j) (v j) x z‖ ^ 2 := by
  rw [OAI.Analysis.Calculus.Current.waveCurrent, OAI.Analysis.Calculus.Current.currentMatrix, timeComponent_outer]
  exact waveCurrentTime_norm_sq κ cR cI v hκ x z hY

end OAI.Analysis.PDE.Concentration
