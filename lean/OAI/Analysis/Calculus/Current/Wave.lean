import OAI.Analysis.Calculus.Current.Expansion

namespace OAI.Analysis.Calculus.Current

noncomputable section
open scoped Topology Matrix

theorem quaternionDivergence_congr_on_nonzero {d : ℕ}
    (F G : Index d → (Index d → ℝ) → (Index d → ℂ) → Quaternion ℝ)
    (heq : ∀ a q w, w none ≠ 0 → F a q w = G a q w)
    (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0) :
    quaternionDivergence F x z = quaternionDivergence G x z := by
  have hr (a : Index d) : quaternionRealD (F a) x z a = quaternionRealD (G a) x z a := by
    unfold quaternionRealD
    congr 1
    funext t
    exact heq a _ z hY
  have hi (a : Index d) (c : ℂ) :
      quaternionImagD (F a) x z a c = quaternionImagD (G a) x z a c := by
    unfold quaternionImagD
    apply Filter.EventuallyEq.deriv_eq
    have hn : ∀ᶠ t : ℝ in 𝓝 0, imaginaryLine z (Pi.single a c) t none ≠ 0 :=
      (hasDerivAt_imaginaryLine z (Pi.single a c) none).continuousAt.eventually_ne
        (by simpa only [imaginaryLine_zero] using hY)
    filter_upwards [hn] with t ht
    exact heq a x _ ht
  unfold quaternionDivergence
  apply Finset.sum_congr rfl
  intro a _
  rw [hr, hi, hi]

/-- The outer-product current itself, not just separately supplied pairs, has
zero three-real-slot quaternionic divergence. -/
theorem modeCurrent_divergence {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) (b : Index d) :
    quaternionDivergence (fun a q w => modeCurrent κ cR cI v q w a b) x z = 0 := by
  rw [quaternionDivergence_congr_on_nonzero _ _
    (fun a q w hw => modeCurrent_paired_expansion κ cR cI v q w hw a b) x z hY]
  exact wavePairedQuaternion_finset_divergence Finset.univ
    (fun p : ι × ι => κ p.1) (fun p : ι × ι => κ p.2)
    (fun p : ι × ι => (1 / 2 : ℝ) * crossReal (cR p.1) (cI p.1) (cR p.2) (cI p.2))
    (fun p : ι × ι => (1 / 2 : ℝ) * crossImag (cR p.1) (cI p.1) (cR p.2) (cI p.2))
    (fun p : ι × ι => v p.1) (fun p : ι × ι => v p.2) x z hY b

def frequencyNormalization (d : ℕ) (κ : ℝ) : ℝ := κ ^ ((d : ℝ) / 2)

def normalizedModeAmplitude {d : ℕ} (κ cR cI : ℝ) (v : Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) : Quaternion ℝ :=
  modeAmplitude κ (frequencyNormalization d κ * cR) (frequencyNormalization d κ * cI) v x z

theorem phaseComplex_scale {d : ℕ} (r cR cI : ℝ) (L x : Index d → ℝ) :
    phaseComplex (r * cR) (r * cI) L x = (r : ℂ) * phaseComplex cR cI L x := by
  apply Complex.ext <;> simp [phaseComplex, phaseF_scale, phaseG_scale]

theorem normalizedEnvelope_formula {d : ℕ} (κ : ℝ) (hκ : 0 < κ)
    (v : Fin d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0) :
    frequencyNormalization d κ * modeEnvelope κ v z =
      (κ / ‖z none‖) ^ ((d : ℝ) / 2) *
        Real.exp (-κ * ‖z none‖ / 2 * squaredDistance (ratio z) v) := by
  have hy : 0 < ‖z none‖ := norm_pos_iff.mpr hY
  rw [Real.div_rpow hκ.le hy.le, Real.rpow_def_of_pos hy]
  unfold frequencyNormalization modeEnvelope
  rw [show -(d : ℝ) / 2 * Real.log ‖z none‖ -
      κ * ‖z none‖ / 2 * squaredDistance (ratio z) v =
      -(Real.log ‖z none‖ * ((d : ℝ) / 2)) +
        (-κ * ‖z none‖ / 2 * squaredDistance (ratio z) v) by ring,
    Real.exp_add, Real.exp_neg]
  ring

/-- Exact manuscript amplitude, including `(κ/y)^(d/2)`; the equality links
the normalization-absorbed proof to the original definition. -/
theorem normalizedModeAmplitude_formula {d : ℕ} (κ cR cI : ℝ) (hκ : 0 < κ)
    (v : Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ) (hY : z none ≠ 0) :
    normalizedModeAmplitude κ cR cI v x z =
      movingEmbed (movingUnit z)
        (((κ / ‖z none‖) ^ ((d : ℝ) / 2) *
          Real.exp (-κ * ‖z none‖ / 2 * squaredDistance (ratio z) v) : ℝ) *
          phaseComplex cR cI (modeCovector κ v) x) := by
  unfold normalizedModeAmplitude modeAmplitude
  rw [phaseComplex_scale, ← normalizedEnvelope_formula κ hκ v z hY]
  congr 1
  push_cast
  ring

def waveCurrent {d : ℕ} {ι : Type*} [Fintype ι] (κ cR cI : ι → ℝ)
    (v : ι → Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ) :
    Matrix (Index d) (Index d) (Quaternion ℝ) :=
  currentMatrix (ratio z) (fun j i => (v j i : ℂ))
    (fun j => normalizedModeAmplitude (κ j) (cR j) (cI j) (v j) x z)

theorem waveCurrent_divergence {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) (b : Index d) :
    quaternionDivergence (fun a q w => waveCurrent κ cR cI v q w a b) x z = 0 :=
  modeCurrent_divergence κ
    (fun j => frequencyNormalization d (κ j) * cR j)
    (fun j => frequencyNormalization d (κ j) * cI j) v x z hY b

theorem waveCurrent_isHermitian {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ) :
    (waveCurrent κ cR cI v x z).IsHermitian :=
  currentMatrix_isHermitian _ _ _

theorem waveCurrent_quadratic_nonneg {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ)
    (ξ : Index d → Quaternion ℝ) :
    0 ≤ (∑ a, star (ξ a) * (waveCurrent κ cR cI v x z *ᵥ ξ) a).re :=
  currentMatrix_quadratic_nonneg _ _ _ _

theorem waveCurrent_image_tangent {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ)
    (ξ : Index d → Quaternion ℝ) :
    ∑ a, complexK (phaseRow (ratio z) a) * (waveCurrent κ cR cI v x z *ᵥ ξ) a = 0 :=
  currentMatrix_image_tangent _ _ _ _

end
end OAI.Analysis.Calculus.Current
