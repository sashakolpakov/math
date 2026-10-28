import OAI.RepresentationTheory.Theta.Analytic
import OAI.AlgebraicGeometry.ComplexMultiplication.SparseLatticeSums

/-! # Gaussian Convergence Gaussian -/

namespace OAI.Analysis.Theta.GaussianConvergenceGaussian.Construction

noncomputable section

section

open scoped Classical BigOperators _root_.Topology
open Filter Set _root_.Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma iteratedDeriv_cexp (k : ℕ) : iteratedDeriv k Complex.exp = Complex.exp := by
  induction k with
  | zero => simp
  | succ k hk => rw [iteratedDeriv_succ, hk]; exact Complex.deriv_exp

lemma exponential_derivative_bound (a : ℂ) (l : E →L[ℂ] ℂ) (k : ℕ) (p : E) :
    ‖iteratedFDeriv ℂ k (fun q => a * Complex.exp (l q)) p‖ ≤
      ‖a * Complex.exp (l p)‖ * ‖l‖ ^ k := by
  have hf : ContDiff ℂ k (fun q => Complex.exp (l q)) :=
    Complex.contDiff_exp.comp l.contDiff
  rw [show (fun q => a * Complex.exp (l q)) =
      (fun q => a • Complex.exp (l q)) from rfl,
    iteratedFDeriv_const_smul_apply' hf.contDiffAt, norm_smul]
  have hc := l.iteratedFDeriv_comp_right (Complex.contDiff_exp (n := k)) p le_rfl
  change ‖a‖ * ‖iteratedFDeriv ℂ k (Complex.exp ∘ l) p‖ ≤ _
  rw [hc]
  calc
    _ ≤ ‖a‖ * (‖iteratedFDeriv ℂ k Complex.exp (l p)‖ * ‖l‖ ^ k) := by
      gcongr
      simpa using (iteratedFDeriv ℂ k Complex.exp (l p)).norm_compContinuousLinearMap_le
        (fun _ : Fin k => l)
    _ = _ := by rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp, norm_mul]; ring

lemma hasSum_iteratedFDeriv_on_ball
    {I : Type*} (f : I → E → ℂ)
    (hf : ∀ i, ContDiff ℂ ⊤ (f i))
    (p : E) (r : ℝ) (hr : 0 < r)
    (v : ℕ → I → ℝ) (hv : ∀ k, Summable (v k))
    (hb : ∀ k i q, q ∈ ball p r → ‖iteratedFDeriv ℂ k (f i) q‖ ≤ v k i) :
    ∀ k q, q ∈ ball p r →
      HasSum (fun i => iteratedFDeriv ℂ k (f i) q)
        (iteratedFDeriv ℂ k (fun z => ∑' i, f i z) q) := by
  intro k
  induction k with
  | zero =>
    intro q hq
    have hs : Summable (fun i => f i q) :=
      .of_norm_bounded (hv 0) (fun i => by simpa using hb 0 i q hq)
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply] using!
      hs.hasSum.map (continuousMultilinearCurryFin0 ℂ E ℂ).symm.toContinuousLinearEquiv
        (continuousMultilinearCurryFin0 ℂ E ℂ).symm.continuous
  | succ k ih =>
    intro q hq
    have hd (i : I) : Differentiable ℂ (iteratedFDeriv ℂ k (f i)) :=
      (hf i).differentiable_iteratedFDeriv (by simp)
    have hbound (i : I) (z : E) (hz : z ∈ ball p r) :
        ‖fderiv ℂ (iteratedFDeriv ℂ k (f i)) z‖ ≤ v (k + 1) i := by
      simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
        LinearIsometryEquiv.norm_map] using hb (k + 1) i z hz
    have hdSum := hasFDerivAt_tsum_of_isPreconnected (hv (k + 1))
      isOpen_ball (convex_ball p r).isPreconnected
      (fun i z _ => (hd i z).hasFDerivAt) hbound
      (mem_ball_self hr) (ih p (mem_ball_self hr)).summable hq
    have heq : (fun z => ∑' i, iteratedFDeriv ℂ k (f i) z) =ᶠ[𝓝 q]
        iteratedFDeriv ℂ k (fun z => ∑' i, f i z) :=
      Filter.mem_of_superset (isOpen_ball.mem_nhds hq) (fun z hz => (ih z hz).tsum_eq)
    have hs : Summable (fun i => iteratedFDeriv ℂ (k + 1) (f i) q) :=
      .of_norm_bounded (hv (k + 1)) (fun i => hb (k + 1) i q hq)
    convert hs.hasSum using 1
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    rw [← heq.fderiv_eq, hdSum.fderiv]
    exact (continuousMultilinearCurryLeftEquiv ℂ
      (fun _ : Fin (k + 1) => E) ℂ).symm.toContinuousLinearEquiv.map_tsum

end

section

open scoped Classical BigOperators _root_.Topology BoundedContinuousFunction _root_.Matrix.Norms.Elementwise
open Filter Set _root_.Metric OAI.AlgebraicGeometry.ComplexMultiplication.SparseLatticeSums.CM OAI.RepresentationTheory.Theta.Analytic

variable {ι : Type*} [Fintype ι]

/-- The unfolded matrix type keeps operator-norm instance synthesis transparent. -/
abbrev ThetaParameters (ι : Type*) := (ι → ι → ℂ) × (ι → ℂ)

local instance : NormedAddCommGroup (ThetaParameters ι) := inferInstance
local instance : NormedSpace ℂ (ThetaParameters ι) := inferInstance

def thetaSummand (L : Submodule ℤ (ι → ℝ)) (φ : L →ᵇ ℂ)
    (x : L) (p : ThetaParameters ι) : ℂ :=
  φ x * Complex.exp
    ((Real.pi : ℂ) * Complex.I *
        AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm p.1 (x : ι → ℝ) (x : ι → ℝ) +
      (2 * (Real.pi : ℂ) * Complex.I) *
        (∑ i, (((x : ι → ℝ) i : ℝ) : ℂ) * p.2 i))

local instance : NormedAddCommGroup ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ) := inferInstance
local instance : NormedSpace ℂ ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ) := inferInstance

def parameterMap : ThetaParameters ι →L[ℂ]
    (RepresentationTheory.Theta.Analytic.PhaseParameter (ι → ℝ) × (ι → ℂ)) :=
  RepresentationTheory.Theta.Analytic.coordinatePhaseMap.prodMap (ContinuousLinearMap.id ℂ (ι → ℂ))

def coordinateExponent (x : ι → ℝ) : ThetaParameters ι →L[ℂ] ℂ :=
  (RepresentationTheory.Theta.Analytic.phaseExponent (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι) x).comp parameterMap

lemma thetaSummand_eq (L : Submodule ℤ (ι → ℝ)) (φ : L →ᵇ ℂ) (x : L) :
    thetaSummand L φ x = fun p => φ x * Complex.exp (coordinateExponent (x : ι → ℝ) p) := by
  funext p
  change φ x * Complex.exp _ = φ x * Complex.exp
    (RepresentationTheory.Theta.Analytic.phaseExponent (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι) (x : ι → ℝ)
      (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm p.1, p.2))
  rw [RepresentationTheory.Theta.Analytic.phaseExponent_apply, AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing_apply]

lemma coordinateExponent_norm_bound :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ x : ι → ℝ,
      ‖coordinateExponent x‖ ≤ D * (1 + ‖x‖) ^ 2 := by
  let A := Real.pi + 2 * Real.pi * ‖AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι‖
  let D := 1 + A * ‖parameterMap (ι := ι)‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨D, by dsimp [D]; linarith [mul_nonneg hA (norm_nonneg (parameterMap (ι := ι)))], fun x => ?_⟩
  have hx := norm_nonneg x
  have h1 : ‖x‖ ^ 2 ≤ (1 + ‖x‖) ^ 2 := by nlinarith
  have h2 : ‖x‖ ≤ (1 + ‖x‖) ^ 2 := by nlinarith [sq_nonneg ‖x‖]
  calc
    ‖coordinateExponent x‖ ≤ ‖RepresentationTheory.Theta.Analytic.phaseExponent (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι) x‖ * ‖parameterMap (ι := ι)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (Real.pi * ‖x‖ ^ 2 + 2 * Real.pi * ‖AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι‖ * ‖x‖) *
        ‖parameterMap (ι := ι)‖ := by gcongr; exact RepresentationTheory.Theta.Analytic.phaseExponent_norm_le _ x
    _ ≤ (A * (1 + ‖x‖) ^ 2) * ‖parameterMap (ι := ι)‖ := by
      have ht := add_le_add (mul_le_mul_of_nonneg_left h1 Real.pi_pos.le)
        (mul_le_mul_of_nonneg_left h2
          (show 0 ≤ 2 * Real.pi * ‖AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι‖ by positivity))
      have ht' := mul_le_mul_of_nonneg_right ht (norm_nonneg (parameterMap (ι := ι)))
      simpa only [A, add_mul] using ht'
    _ ≤ D * (1 + ‖x‖) ^ 2 := by dsimp [D]; nlinarith [sq_nonneg (1 + ‖x‖)]

lemma compact_quadratic_lower_bound
    (K : Set (ThetaParameters ι)) (hK : IsCompact K)
    (hKpos : ∀ p ∈ K, p.1 ∈ RepresentationTheory.Theta.Definitions.siegelDomain) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ K, ∀ x : ι → ℝ,
      c * ‖x‖ ^ 2 ≤ (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm p.1 x x).im := by
  apply hK.induction_on (p := fun S => ∃ c : ℝ, 0 < c ∧ ∀ p ∈ S, ∀ x : ι → ℝ,
    c * ‖x‖ ^ 2 ≤ (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm p.1 x x).im)
  · exact ⟨1, zero_lt_one, by simp⟩
  · rintro S T hST ⟨c, hc, hbound⟩
    exact ⟨c, hc, fun p hp => hbound p (hST hp)⟩
  · rintro S T ⟨c, hc, hS⟩ ⟨d, hd, hT⟩
    refine ⟨min c d, lt_min hc hd, fun p hp x => ?_⟩
    rcases hp with hp | hp
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans (hS p hp x)
    · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans (hT p hp x)
  · intro p hp
    let Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι := ⟨p.1, (hKpos p hp).1, (hKpos p hp).2⟩
    let c := Z.phase.lowerBound / 2
    have hc : 0 < c := half_pos Z.phase.lowerBound_pos
    let S : Set (ThetaParameters ι) :=
      {q | ‖AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm q.1 - Z.phase.form‖ < c}
    have hSopen : IsOpen S :=
      isOpen_lt (((AlgebraicGeometry.ComplexMultiplication.ThetaCovariance.CM.thetaMatrixPhaseMap (ι := ι)).continuous.comp continuous_fst).sub
        continuous_const).norm continuous_const
    have hpS : p ∈ S := by change ‖AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm p.1 - AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm p.1‖ < c; simpa
    refine ⟨S, mem_nhdsWithin_of_mem_nhds (hSopen.mem_nhds hpS), c, hc, ?_⟩
    intro q hq x
    exact Z.phase.nearby_phase_imaginary_lower_bound (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm q.1) hq.le x

end

open scoped Classical BigOperators _root_.Topology BoundedContinuousFunction _root_.Matrix.Norms.Elementwise
open Filter Set _root_.Metric OAI.AlgebraicGeometry.ComplexMultiplication.SparseLatticeSums.CM OAI.RepresentationTheory.Theta.Analytic

variable {ι : Type*} [Fintype ι]

local instance : NormedAddCommGroup (ThetaParameters ι) := inferInstance
local instance : NormedSpace ℂ (ThetaParameters ι) := inferInstance
local instance : NormedAddCommGroup ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ) := inferInstance
local instance : NormedSpace ℂ ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ) := inferInstance

lemma shifted_gaussian_summable (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    (C c b : ℝ) (hC : 0 ≤ C) (hc : 0 < c) (d : ℕ) :
    Summable (fun x : L => C * (1 + ‖(x : ι → ℝ)‖) ^ d *
      Real.exp (-c * ‖(x : ι → ℝ)‖ ^ 2 + b * ‖(x : ι → ℝ)‖)) := by
  apply ((AlgebraicGeometry.ComplexMultiplication.LatticeGaussian.CM.lattice_gaussian_poly_summable L c b hc d).mul_left (C * 2 ^ d)).of_norm_bounded_eventually
  filter_upwards [(AlgebraicGeometry.ComplexMultiplication.LatticeGaussian.CM.lattice_norm_tendsto_cofinite L).eventually (eventually_ge_atTop (1 : ℝ))]
    with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  change C * (1 + ‖(x : ι → ℝ)‖) ^ d * _ ≤ (C * 2 ^ d) * (‖(x : ι → ℝ)‖ ^ d * _)
  calc
    _ ≤ C * (2 * ‖(x : ι → ℝ)‖) ^ d *
        Real.exp (-c * ‖(x : ι → ℝ)‖ ^ 2 + b * ‖(x : ι → ℝ)‖) := by
      gcongr
      change 1 ≤ ‖(x : ι → ℝ)‖ at hx
      linarith
    _ = _ := by
      have hn : ‖x‖ = ‖(x : ι → ℝ)‖ := rfl
      simp only [mul_pow, hn]
      ring

lemma thetaSummand_gaussian_bound
    (L : Submodule ℤ (ι → ℝ)) (φ : L →ᵇ ℂ)
    (p : ThetaParameters ι) (c R : ℝ)
    (hq : ∀ x : ι → ℝ, c * ‖x‖ ^ 2 ≤ (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm p.1 x x).im)
    (hR : ‖p.2‖ ≤ R) (x : L) :
    ‖thetaSummand L φ x p‖ ≤ ‖φ‖ * Real.exp
      (-(Real.pi * c) * ‖(x : ι → ℝ)‖ ^ 2 +
        (2 * Real.pi * ‖AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι‖ * R) * ‖(x : ι → ℝ)‖) := by
  let P := AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι
  have hlin : -(P (x : ι → ℝ) p.2).im ≤ ‖P‖ * ‖(x : ι → ℝ)‖ * R :=
    (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans
      ((AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.pairing_norm_le P x p.2).trans
        (mul_le_mul_of_nonneg_left hR (mul_nonneg (norm_nonneg P) (norm_nonneg _)))))
  have he : ‖Complex.exp (coordinateExponent (x : ι → ℝ) p)‖ ≤ Real.exp
      (-(Real.pi * c) * ‖(x : ι → ℝ)‖ ^ 2 +
        (2 * Real.pi * ‖P‖ * R) * ‖(x : ι → ℝ)‖) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    change (RepresentationTheory.Theta.Analytic.phaseExponent P (x : ι → ℝ) (parameterMap p)).re ≤ _
    rw [RepresentationTheory.Theta.Analytic.phaseExponent_apply]
    change (((Real.pi : ℂ) * Complex.I * AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm p.1 (x : ι → ℝ) (x : ι → ℝ)) +
      (2 * (Real.pi : ℂ) * Complex.I) * P (x : ι → ℝ) p.2).re ≤ _
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero,
      add_zero, mul_one, Complex.re_ofNat, Complex.im_ofNat]
    have hquad := mul_le_mul_of_nonneg_left (hq x) Real.pi_pos.le
    have hl := mul_le_mul_of_nonneg_left hlin (show 0 ≤ 2 * Real.pi by positivity)
    nlinarith
  rw [thetaSummand_eq, norm_mul]
  exact mul_le_mul (φ.norm_coe_le_norm x) he (norm_nonneg _) (norm_nonneg _)

lemma gaussian_majorant_on_set
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] (φ : L →ᵇ ℂ)
    (S : Set (ThetaParameters ι)) (c R : ℝ) (hc : 0 < c) (hR0 : 0 ≤ R)
    (hq : ∀ p ∈ S, ∀ x : ι → ℝ, c * ‖x‖ ^ 2 ≤ (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm p.1 x x).im)
    (hR : ∀ p ∈ S, ‖p.2‖ ≤ R) (m : ℕ) :
    ∃ C c' b : ℝ,
      let M : L → ℝ := fun x => C * (1 + ‖(x : ι → ℝ)‖) ^ (2 * m) *
        Real.exp (-c' * ‖(x : ι → ℝ)‖ ^ 2 + b * ‖(x : ι → ℝ)‖)
      0 < C ∧ 0 < c' ∧ 0 ≤ b ∧ Summable M ∧
        ∀ k ≤ m, ∀ x : L, ∀ p ∈ S,
          ‖iteratedFDeriv ℂ k (thetaSummand L φ x) p‖ ≤ M x := by
  obtain ⟨D, hD, hDbound⟩ := coordinateExponent_norm_bound (ι := ι)
  let C := (‖φ‖ + 1) * D ^ m
  let b := 2 * Real.pi * ‖AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι‖ * R
  have hC : 0 < C := mul_pos (by positivity) (pow_pos (lt_of_lt_of_le zero_lt_one hD) m)
  refine ⟨C, Real.pi * c, b, hC, mul_pos Real.pi_pos hc, by dsimp [b]; positivity,
    shifted_gaussian_summable L C (Real.pi * c) b hC.le (mul_pos Real.pi_pos hc) (2 * m), ?_⟩
  intro k hk x p hp
  have hpow : ‖coordinateExponent (x : ι → ℝ)‖ ^ k ≤ D ^ m * (1 + ‖(x : ι → ℝ)‖) ^ (2 * m) := by
    calc
      _ ≤ (D * (1 + ‖(x : ι → ℝ)‖) ^ 2) ^ k := by gcongr; exact hDbound x
      _ ≤ (D * (1 + ‖(x : ι → ℝ)‖) ^ 2) ^ m := by
        apply pow_le_pow_right₀ _ hk
        exact one_le_mul_of_one_le_of_one_le hD (one_le_pow₀ (by linarith [norm_nonneg (x : ι → ℝ)]))
      _ = _ := by rw [mul_pow, ← pow_mul]
  have he := thetaSummand_gaussian_bound L φ p c R (hq p hp) (hR p hp) x
  have hd : ‖iteratedFDeriv ℂ k (thetaSummand L φ x) p‖ ≤
      ‖thetaSummand L φ x p‖ * ‖coordinateExponent (x : ι → ℝ)‖ ^ k := by
    simpa only [thetaSummand_eq] using
      exponential_derivative_bound (φ x) (coordinateExponent (x : ι → ℝ)) k p
  calc
    _ ≤ ‖thetaSummand L φ x p‖ * ‖coordinateExponent (x : ι → ℝ)‖ ^ k := hd
    _ ≤ (‖φ‖ * Real.exp (-(Real.pi * c) * ‖(x : ι → ℝ)‖ ^ 2 + b * ‖(x : ι → ℝ)‖)) *
        (D ^ m * (1 + ‖(x : ι → ℝ)‖) ^ (2 * m)) := by
      exact mul_le_mul he hpow (by positivity) (by positivity)
    _ ≤ C * (1 + ‖(x : ι → ℝ)‖) ^ (2 * m) *
        Real.exp (-(Real.pi * c) * ‖(x : ι → ℝ)‖ ^ 2 + b * ‖(x : ι → ℝ)‖) := by
      dsimp [C]
      nlinarith [mul_nonneg (pow_nonneg (le_trans zero_le_one hD) m)
        (mul_nonneg (pow_nonneg (by positivity : 0 ≤ 1 + ‖(x : ι → ℝ)‖) (2 * m))
          (Real.exp_pos (-(Real.pi * c) * ‖(x : ι → ℝ)‖ ^ 2 + b * ‖(x : ι → ℝ)‖)).le)]

lemma positive_ball_bounds (p : ThetaParameters ι) (hp : p.1 ∈ RepresentationTheory.Theta.Definitions.siegelDomain) :
    ∃ r c R : ℝ, 0 < r ∧ 0 < c ∧ 0 ≤ R ∧
      (∀ q ∈ ball p r, ∀ x : ι → ℝ,
        c * ‖x‖ ^ 2 ≤ (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm q.1 x x).im) ∧
      (∀ q ∈ ball p r, ‖q.2‖ ≤ R) := by
  let Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι := ⟨p.1, hp.1, hp.2⟩
  let c := Z.phase.lowerBound / 2
  have hc : 0 < c := half_pos Z.phase.lowerBound_pos
  let S : Set (ThetaParameters ι) := {q | ‖AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm q.1 - Z.phase.form‖ < c}
  have hSopen : IsOpen S :=
    isOpen_lt (((AlgebraicGeometry.ComplexMultiplication.ThetaCovariance.CM.thetaMatrixPhaseMap (ι := ι)).continuous.comp continuous_fst).sub
      continuous_const).norm continuous_const
  have hpS : p ∈ S := by
    change ‖AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm p.1 - AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm p.1‖ < c
    simpa only [sub_self, norm_zero] using hc
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hSopen p hpS
  refine ⟨r, c, ‖p.2‖ + r, hr, hc, by positivity, ?_, ?_⟩
  · intro q hq x
    exact Z.phase.nearby_phase_imaginary_lower_bound (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm q.1) (hball hq).le x
  · intro q hq
    have hd : ‖q.2 - p.2‖ < r :=
      (norm_snd_le (q - p)).trans_lt (by simpa [mem_ball, dist_eq_norm] using hq)
    have hn := norm_le_norm_sub_add q.2 p.2
    linarith

lemma thetaSummand_contDiff (L : Submodule ℤ (ι → ℝ)) (φ : L →ᵇ ℂ) (x : L) :
    ContDiff ℂ ⊤ (thetaSummand L φ x) := by
  rw [thetaSummand_eq]
  exact contDiff_const.mul (Complex.contDiff_exp.comp (coordinateExponent (x : ι → ℝ)).contDiff)

lemma theta_derivative_hasSum
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] (φ : L →ᵇ ℂ)
    (p : ThetaParameters ι) (hp : p.1 ∈ RepresentationTheory.Theta.Definitions.siegelDomain) (k : ℕ) :
    HasSum (fun x : L => iteratedFDeriv ℂ k (thetaSummand L φ x) p)
      (iteratedFDeriv ℂ k (fun q : ThetaParameters ι => RepresentationTheory.Theta.Definitions.theta L φ q.1 q.2) p) := by
  obtain ⟨r, c, R, hr, hc, hR0, hquad, hR⟩ := positive_ball_bounds p hp
  have hm : ∀ n : ℕ, ∃ M : L → ℝ, Summable M ∧
      ∀ x q, q ∈ ball p r → ‖iteratedFDeriv ℂ n (thetaSummand L φ x) q‖ ≤ M x := by
    intro n
    obtain ⟨C, c', b, _, _, _, hs, hb⟩ :=
      gaussian_majorant_on_set L φ (ball p r) c R hc hR0 hquad hR n
    exact ⟨_, hs, fun x q hq => hb n le_rfl x q hq⟩
  choose M hM hMb using hm
  exact hasSum_iteratedFDeriv_on_ball (thetaSummand L φ) (thetaSummand_contDiff L φ)
    p r hr M hM (fun n x q hq => hMb n x q hq) k p (mem_ball_self hr)

end

end OAI.Analysis.Theta.GaussianConvergenceGaussian.Construction
