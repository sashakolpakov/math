import OAI.RepresentationTheory.Theta.CosetPoisson
import OAI.RepresentationTheory.Theta.CosetTests
import OAI.RepresentationTheory.Theta.AdelicTopology
import OAI.RepresentationTheory.Theta.Generators

/-! # Poisson Automorphy Gaussian Poisson -/

namespace OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction

noncomputable section

section

/-! Adelic Poisson summation and rational theta invariance for the supplied Weil data. -/

open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)

theorem theta_weyl_coset (f : PoissonAutomorphyNormalizationData.realSchwartz ι) (n : ℕ) (hn : 0 < n) (a : ι → ℚ) :
    PoissonAutomorphyNormalizationData.thetaFunctional (D.rationalAction (Generators.PoissonAutomorphyConstruction.weyl ι)
      (PoissonAutomorphyNormalizationData.tensor f (CosetTests.PoissonAutomorphyConstruction.latticeCosetTest (n : ℚ) (by exact_mod_cast hn.ne') (PoissonAutomorphyNormalizationData.finiteDiagonal a)))) =
    PoissonAutomorphyNormalizationData.thetaFunctional (PoissonAutomorphyNormalizationData.tensor f (CosetTests.PoissonAutomorphyConstruction.latticeCosetTest (n : ℚ) (by exact_mod_cast hn.ne') (PoissonAutomorphyNormalizationData.finiteDiagonal a))) := by
  let φ := CosetTests.PoissonAutomorphyConstruction.latticeCosetTest (n : ℚ) (by exact_mod_cast hn.ne') (PoissonAutomorphyNormalizationData.finiteDiagonal a)
  obtain ⟨F, hF⟩ := (PoissonAutomorphyNormalizationData.Construction.realSchwartz_mem_iff f.val).mp f.property
  calc
    _ = ∑' x : ι → ℚ, PoissonAutomorphyNormalizationData.fourier PoissonAutomorphyNormalizationData.standardRealCharacter MeasureTheory.volume f.val (PoissonAutomorphyNormalizationData.Construction.rationalReal x) *
        PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure φ.val (PoissonAutomorphyNormalizationData.finiteDiagonal x) := by
      apply tsum_congr
      intro x
      exact (D.rational_fourier (Generators.PoissonAutomorphyConstruction.weyl ι) rfl (PoissonAutomorphyNormalizationData.tensor f φ) (PoissonAutomorphyNormalizationData.diagonal x)).trans
        (AdelicTopology.PoissonAutomorphyConstruction.adelic_fourier_pureTensor D f φ (PoissonAutomorphyNormalizationData.diagonal x))
    _ = _ := by
      change (∑' x : ι → ℚ, PoissonAutomorphyNormalizationData.fourier PoissonAutomorphyNormalizationData.standardRealCharacter MeasureTheory.volume f.val (PoissonAutomorphyNormalizationData.Construction.rationalReal x) *
        PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure
          (PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator (n : ℚ) (by exact_mod_cast hn.ne') (PoissonAutomorphyNormalizationData.finiteDiagonal a)) (PoissonAutomorphyNormalizationData.finiteDiagonal x)) =
        ∑' x : ι → ℚ, f.val (PoissonAutomorphyNormalizationData.Construction.rationalReal x) *
          PoissonAutomorphyFiniteFourier.Construction.latticeCosetIndicator (n : ℚ) (by exact_mod_cast hn.ne') (PoissonAutomorphyNormalizationData.finiteDiagonal a) (PoissonAutomorphyNormalizationData.finiteDiagonal x)
      rw [hF]
      exact (CosetPoisson.AutomorphyConstruction.coset_poisson_summation D n hn a F).symm

theorem theta_weyl_tensor (f : PoissonAutomorphyNormalizationData.realSchwartz ι) (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    PoissonAutomorphyNormalizationData.thetaFunctional (D.rationalAction (Generators.PoissonAutomorphyConstruction.weyl ι) (PoissonAutomorphyNormalizationData.tensor f φ)) = PoissonAutomorphyNormalizationData.thetaFunctional (PoissonAutomorphyNormalizationData.tensor f φ) := by
  let A : PoissonAutomorphyNormalizationData.finiteSchwartz ι →ₗ[ℂ] ℂ :=
    (Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional.comp (D.rationalAction (Generators.PoissonAutomorphyConstruction.weyl ι)).toLinearMap).comp (CosetTests.PoissonAutomorphyConstruction.tensorLeft f)
  let B : PoissonAutomorphyNormalizationData.finiteSchwartz ι →ₗ[ℂ] ℂ := Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional.comp (CosetTests.PoissonAutomorphyConstruction.tensorLeft f)
  change A φ = B φ
  obtain ⟨n, hn, s, hφ⟩ := CosetTests.PoissonAutomorphyConstruction.finiteSchwartz_coset_expansion_eq φ
  rw [hφ]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  exact theta_weyl_coset D f n hn (PoissonAutomorphyFiniteFourier.Construction.finiteQuotientRep (n : ℚ) (by exact_mod_cast hn.ne') c)

theorem theta_weyl_invariant (f : PoissonAutomorphyNormalizationData.adelicSchwartz ι) :
    PoissonAutomorphyNormalizationData.thetaFunctional (D.rationalAction (Generators.PoissonAutomorphyConstruction.weyl ι) f) = PoissonAutomorphyNormalizationData.thetaFunctional f := by
  let A : PoissonAutomorphyNormalizationData.adelicSchwartz ι →ₗ[ℂ] ℂ :=
    Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional.comp (D.rationalAction (Generators.PoissonAutomorphyConstruction.weyl ι)).toLinearMap
  let B : PoissonAutomorphyNormalizationData.adelicSchwartz ι →ₗ[ℂ] ℂ := Convergence.PoissonAutomorphyConstruction.thetaLinearFunctional
  change A f = B f
  rcases f with ⟨f, hf⟩
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨g, φ, rfl⟩ := hf
      exact theta_weyl_tensor D g φ
  | zero =>
      change A 0 = B 0
      rw [map_zero, map_zero]
  | add f g hf hg ihf ihg =>
      change A (⟨f, hf⟩ + ⟨g, hg⟩) = B (⟨f, hf⟩ + ⟨g, hg⟩)
      rw [map_add, map_add, ihf, ihg]
  | smul c f hf ih =>
      change A (c • ⟨f, hf⟩) = B (c • ⟨f, hf⟩)
      rw [map_smul, map_smul, ih]

theorem adelic_poisson_summation (f : PoissonAutomorphyNormalizationData.adelicSchwartz ι) :
    (∑' x : ι → ℚ, PoissonAutomorphyNormalizationData.fourier D.character (PoissonAutomorphyNormalizationData.adelicMeasure D.finiteMeasure) f.val (PoissonAutomorphyNormalizationData.diagonal x)) =
      PoissonAutomorphyNormalizationData.thetaFunctional f := by
  calc
    _ = PoissonAutomorphyNormalizationData.thetaFunctional (D.rationalAction (Generators.PoissonAutomorphyConstruction.weyl ι) f) := by
      apply tsum_congr
      intro x
      exact (D.rational_fourier (Generators.PoissonAutomorphyConstruction.weyl ι) rfl f (PoissonAutomorphyNormalizationData.diagonal x)).symm
    _ = _ := theta_weyl_invariant D f

theorem rational_theta_invariant (γ : PoissonAutomorphyNormalizationData.Sp ι ℚ) (f : PoissonAutomorphyNormalizationData.adelicSchwartz ι) :
    PoissonAutomorphyNormalizationData.thetaFunctional (D.rationalAction γ f) = PoissonAutomorphyNormalizationData.thetaFunctional f :=
  Generators.PoissonAutomorphyConstruction.theta_invariant_of_fourier_summation D (adelic_poisson_summation D) γ f

end

section

/-! Polynomial oscillatory factors preserve the real Schwartz space. -/

open scoped Classical

def phaseExp (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

theorem phaseExp_hasDerivAt (t : ℝ) :
    HasDerivAt phaseExp (phaseExp t * Complex.I) t := by
  have h : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I t := by
    simpa using ((hasDerivAt_id t).ofReal_comp).mul_const Complex.I
  exact h.cexp

theorem phaseExp_iteratedDeriv (n : ℕ) :
    iteratedDeriv n phaseExp = fun t => Complex.I ^ n * phaseExp t := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      rw [((phaseExp_hasDerivAt t).const_mul (Complex.I ^ n)).deriv]
      rw [pow_succ]
      ring

theorem phaseExp_norm (t : ℝ) : ‖phaseExp t‖ = 1 := by
  simp [phaseExp, Complex.norm_exp]

theorem phaseExp_temperate : Function.HasTemperateGrowth phaseExp := by
  refine ⟨?_, fun n => ⟨0, 1, fun t => ?_⟩⟩
  · unfold phaseExp
    exact (Complex.ofRealCLM.contDiff.mul contDiff_const).cexp
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, phaseExp_iteratedDeriv]
    simp [norm_pow, phaseExp_norm]

variable {ι : Type*} [Fintype ι]

def realChirpPhase (B : Matrix ι ι ℝ) (p : ι → ℝ) (x : ι → ℝ) : ℝ :=
  Real.pi * (∑ i, ∑ j, x i * B i j * x j) + 2 * Real.pi * ∑ i, x i * p i

theorem realChirpPhase_temperate (B : Matrix ι ι ℝ) (p : ι → ℝ) :
    Function.HasTemperateGrowth (realChirpPhase B p) := by
  have hc (i : ι) : Function.HasTemperateGrowth (fun x : ι → ℝ => x i) :=
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasTemperateGrowth
  have hq : Function.HasTemperateGrowth (fun x : ι → ℝ => ∑ i, ∑ j, x i * B i j * x j) :=
    .sum (fun i _ => .sum (fun j _ => ((hc i).mul (.const (B i j))).mul (hc j)))
  have hp : Function.HasTemperateGrowth (fun x : ι → ℝ => ∑ i, x i * p i) :=
    .sum (fun i _ => (hc i).mul (.const (p i)))
  exact ((Function.HasTemperateGrowth.const Real.pi).mul hq).add
    ((Function.HasTemperateGrowth.const (2 * Real.pi)).mul hp)

def realChirp (B : Matrix ι ι ℝ) (p : ι → ℝ) (x : ι → ℝ) : ℂ :=
  phaseExp (realChirpPhase B p x)

theorem realChirp_temperate (B : Matrix ι ι ℝ) (p : ι → ℝ) :
    Function.HasTemperateGrowth (realChirp B p) :=
  phaseExp_temperate.comp (realChirpPhase_temperate B p)

def chirpSchwartz (B : Matrix ι ι ℝ) (p : ι → ℝ) (f : SchwartzMap (ι → ℝ) ℂ) :
    SchwartzMap (ι → ℝ) ℂ := SchwartzMap.smulLeftCLM ℂ (realChirp B p) f

theorem chirpSchwartz_apply (B : Matrix ι ι ℝ) (p : ι → ℝ)
    (f : SchwartzMap (ι → ℝ) ℂ) (x : ι → ℝ) :
    chirpSchwartz B p f x = realChirp B p x * f x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (realChirp_temperate B p) f x

end

section

/-! Polynomially controlled exponents with bounded real part give temperate factors. -/

theorem complex_exp_iteratedFDeriv_norm (n : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ n Complex.exp z‖ = Real.exp z.re := by
  have hrestrict := (Complex.contDiff_exp (𝕜 := ℂ) (n := n)).contDiffAt.restrictScalars_iteratedFDeriv
    (𝕜 := ℝ) (x := z)
  rw [← hrestrict]
  change ‖(iteratedFDeriv ℂ n Complex.exp z).restrictScalars ℝ‖ = _
  rw [ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hiter : iteratedDeriv n Complex.exp = Complex.exp := by
    simpa only [one_mul, one_pow] using iteratedDeriv_cexp_const_mul n 1
  rw [hiter, Complex.norm_exp]

theorem exp_temperate_of_re_bounded {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q : V → ℂ) (hQ : Function.HasTemperateGrowth Q)
    (C : ℝ) (hC : ∀ x, (Q x).re ≤ C) :
    Function.HasTemperateGrowth (fun x => Complex.exp (Q x)) := by
  let U : Set ℂ := {z | z.re < C + 1}
  have hU : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
  apply Function.HasTemperateGrowth.comp' (t := U) ?_ hU.uniqueDiffOn
    (Complex.contDiff_exp (𝕜 := ℝ)).contDiffOn ?_ hQ
  · rintro _ ⟨x, rfl⟩
    exact lt_of_le_of_lt (hC x) (by linarith)
  · intro N
    refine ⟨0, Real.exp (C + 1), (Real.exp_pos _).le, fun n _ z hz => ?_⟩
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
      (Complex.contDiff_exp (𝕜 := ℝ) (n := n)).contDiffAt hz,
      complex_exp_iteratedFDeriv_norm]
    simpa only [pow_zero, mul_one] using Real.exp_le_exp.mpr hz.le

theorem real_quadratic_linear_upper (a b : ℝ) (ha : 0 < a) (t : ℝ) :
    -a * t ^ 2 + b * t ≤ b ^ 2 / (4 * a) := by
  have hid : b ^ 2 / (4 * a) - (-a * t ^ 2 + b * t) = a * (t - b / (2 * a)) ^ 2 := by
    field_simp
    ring
  exact sub_nonneg.mp (hid.symm ▸ mul_nonneg ha.le (sq_nonneg _))

end

section

/-! Temperate exponents and Gaussian bounds on the Siegel domain. -/

open scoped Classical

variable {ι : Type*} [Fintype ι]

def gaussianExponent (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) (x : ι → ℝ) : ℂ :=
  (Real.pi : ℂ) * Complex.I * Z.phase.form x x +
    (2 * (Real.pi : ℂ) * Complex.I) * AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι x z

def gaussianFunction (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) (x : ι → ℝ) : ℂ :=
  Complex.exp (gaussianExponent Z z x)

theorem gaussianFunction_eq_phase (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) (x : ι → ℝ) :
    gaussianFunction Z z x = Z.phase.thetaTerm (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι) x z := rfl

theorem gaussianExponent_temperate (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    Function.HasTemperateGrowth (gaussianExponent Z z) := by
  have hquad : Function.HasTemperateGrowth (fun x => Z.phase.form x x) :=
    Z.phase.form.bilinear_hasTemperateGrowth .id .id
  have hc (i : ι) : Function.HasTemperateGrowth (fun x : ι → ℝ => (x i : ℂ)) :=
    (Complex.ofRealCLM.comp (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)).hasTemperateGrowth
  have hlin : Function.HasTemperateGrowth (fun x : ι → ℝ => ∑ i, (x i : ℂ) * z i) :=
    .sum (fun i _ => (hc i).mul (.const (z i)))
  unfold gaussianExponent
  simp only [AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing_apply]
  exact ((Function.HasTemperateGrowth.const ((Real.pi : ℂ) * Complex.I)).mul hquad).add
      ((Function.HasTemperateGrowth.const (2 * (Real.pi : ℂ) * Complex.I)).mul hlin)

theorem gaussianExponent_re_le (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) (x : ι → ℝ) :
    (gaussianExponent Z z x).re ≤ -(Real.pi * Z.phase.lowerBound) * ‖x‖ ^ 2 +
      (2 * Real.pi * ‖AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι‖ * ‖z‖) * ‖x‖ := by
  apply Real.exp_le_exp.mp
  rw [← Complex.norm_exp]
  change ‖Z.phase.thetaTerm (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι) x z‖ ≤ _
  exact Z.phase.thetaTerm_norm_le (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι) ‖z‖ x z le_rfl

theorem coordinate_sum_sq_le (x : ι → ℝ) :
    (∑ i, (x i) ^ 2) ≤ (Fintype.card ι : ℝ) * ‖x‖ ^ 2 := by
  calc
    _ ≤ ∑ _i : ι, ‖x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := pow_le_pow_left₀ (norm_nonneg (x i)) (norm_le_pi_norm x i) 2
      simpa only [Real.norm_eq_abs, sq_abs] using h
    _ = _ := by simp

def gaussianDamping (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) : ℝ :=
  Real.sqrt (Z.phase.lowerBound / (2 * ((Fintype.card ι : ℝ) + 1)))

theorem gaussianDamping_pos (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) : 0 < gaussianDamping Z := by
  apply Real.sqrt_pos.mpr
  exact div_pos Z.phase.lowerBound_pos (by positivity)

theorem gaussianDamping_bound (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    gaussianDamping Z ^ 2 * (Fintype.card ι : ℝ) ≤ Z.phase.lowerBound / 2 := by
  have hden : 0 < 2 * ((Fintype.card ι : ℝ) + 1) := by positivity
  have hs : gaussianDamping Z ^ 2 = Z.phase.lowerBound / (2 * ((Fintype.card ι : ℝ) + 1)) :=
    Real.sq_sqrt (le_of_lt (div_pos Z.phase.lowerBound_pos hden))
  have heq := (eq_div_iff hden.ne').mp hs
  nlinarith [sq_nonneg (gaussianDamping Z)]

def radialExponent (r : ℝ) (x : ι → ℝ) : ℂ :=
  ((Real.pi * r ^ 2 * (∑ i, x i ^ 2) : ℝ) : ℂ)

theorem radialExponent_temperate (r : ℝ) : Function.HasTemperateGrowth (radialExponent (ι := ι) r) := by
  have hc (i : ι) : Function.HasTemperateGrowth (fun x : ι → ℝ => x i) :=
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasTemperateGrowth
  exact Complex.ofRealCLM.hasTemperateGrowth.comp
    ((Function.HasTemperateGrowth.const (Real.pi * r ^ 2)).mul (.sum fun i _ => (hc i).pow 2))

theorem gaussianRemainder_re_bounded (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    ∃ C : ℝ, ∀ x : ι → ℝ,
      (gaussianExponent Z z x + radialExponent (gaussianDamping Z) x).re ≤ C := by
  let a := Real.pi * Z.phase.lowerBound / 2
  let b := 2 * Real.pi * ‖AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι‖ * ‖z‖
  have ha : 0 < a := div_pos (mul_pos Real.pi_pos Z.phase.lowerBound_pos) (by norm_num)
  refine ⟨b ^ 2 / (4 * a), fun x => ?_⟩
  have hrad : Real.pi * gaussianDamping Z ^ 2 * (∑ i, x i ^ 2) ≤ a * ‖x‖ ^ 2 := by
    calc
      _ ≤ Real.pi * gaussianDamping Z ^ 2 * ((Fintype.card ι : ℝ) * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (coordinate_sum_sq_le x) (by positivity)
      _ = (Real.pi * (gaussianDamping Z ^ 2 * (Fintype.card ι : ℝ))) * ‖x‖ ^ 2 := by ring
      _ ≤ (Real.pi * (Z.phase.lowerBound / 2)) * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (gaussianDamping_bound Z) Real.pi_pos.le) (sq_nonneg _)
      _ = _ := by dsimp [a]; ring
  have hQ := gaussianExponent_re_le Z z x
  have hb := real_quadratic_linear_upper a b ha ‖x‖
  simp only [Complex.add_re, radialExponent, Complex.ofReal_re]
  dsimp [a, b] at *
  linarith

theorem gaussianRemainder_temperate (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    Function.HasTemperateGrowth (fun x => Complex.exp
      (gaussianExponent Z z x + radialExponent (gaussianDamping Z) x)) := by
  obtain ⟨C, hC⟩ := gaussianRemainder_re_bounded Z z
  exact exp_temperate_of_re_bounded _
    ((gaussianExponent_temperate Z z).add (radialExponent_temperate (gaussianDamping Z))) C hC

end

section

/-! The full Siegel Gaussian is an actual real Schwartz test function. -/

open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)

theorem scaled_vacuum_formula (F : SchwartzMap (ι → ℝ) ℂ) (hF : D.vacuum.val = F)
    (r : ℝ) (hr : r ≠ 0) (x : ι → ℝ) :
    RealPoisson.AutomorphyConstruction.scaledRealSchwartz r hr F x = Complex.exp (-radialExponent r x) := by
  rw [RealPoisson.AutomorphyConstruction.scaledRealSchwartz_apply, ← hF, D.vacuum_eq]
  congr 1
  simp only [radialExponent, Pi.smul_apply, smul_eq_mul]
  push_cast
  simp only [mul_pow, ← Finset.mul_sum]
  ring

include D in
theorem gaussianFunction_mem_realSchwartz (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    gaussianFunction Z z ∈ PoissonAutomorphyNormalizationData.realSchwartz ι := by
  obtain ⟨F, hF⟩ := (PoissonAutomorphyNormalizationData.Construction.realSchwartz_mem_iff D.vacuum.val).mp D.vacuum.property
  let r := gaussianDamping Z
  let hr : r ≠ 0 := (gaussianDamping_pos Z).ne'
  let R : (ι → ℝ) → ℂ := fun x => Complex.exp (gaussianExponent Z z x + radialExponent r x)
  have hR : Function.HasTemperateGrowth R := gaussianRemainder_temperate Z z
  let G := SchwartzMap.smulLeftCLM ℂ R (RealPoisson.AutomorphyConstruction.scaledRealSchwartz r hr F)
  apply (PoissonAutomorphyNormalizationData.Construction.realSchwartz_mem_iff _).mpr
  refine ⟨G, funext fun x => ?_⟩
  dsimp only [G]
  rw [SchwartzMap.smulLeftCLM_apply_apply hR, smul_eq_mul, scaled_vacuum_formula D F hF]
  dsimp only [R, gaussianFunction]
  rw [← Complex.exp_add]
  congr 1
  ring

def gaussianTest (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) : PoissonAutomorphyNormalizationData.realSchwartz ι :=
  ⟨gaussianFunction Z z, gaussianFunction_mem_realSchwartz D Z z⟩

theorem gaussianTest_apply (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) (x : ι → ℝ) :
    (gaussianTest D Z z).val x = gaussianFunction Z z x := rfl

theorem thetaFunctional_gaussian_tensor (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    PoissonAutomorphyNormalizationData.thetaFunctional (PoissonAutomorphyNormalizationData.tensor (gaussianTest D Z z) φ) = PoissonAutomorphyNormalizationData.theta φ Z z := by
  apply tsum_congr
  intro x
  change gaussianFunction Z z (PoissonAutomorphyNormalizationData.Construction.rationalReal x) * φ.val (PoissonAutomorphyNormalizationData.finiteDiagonal x) = PoissonAutomorphyNormalizationData.thetaTerm φ Z z x
  rw [Convergence.PoissonAutomorphyConstruction.thetaTerm_eq_weightedPhase, gaussianFunction_eq_phase]
  exact mul_comm _ _

end

/-! Real simultaneous diagonalization of the real and imaginary parts of a Siegel matrix. -/

open scoped Classical MatrixOrder
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem posDef_real_factorization (Y : Matrix ι ι ℝ) (hY : Y.PosDef) :
    ∃ P : Matrix ι ι ℝ, P.det ≠ 0 ∧ P.transpose * P = Y := by
  obtain ⟨P, hP⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.posSemidef.nonneg
  have hreal : P.transpose * P = Y := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hP.symm
  refine ⟨P, ?_, hreal⟩
  intro hz
  have h := hY.det_pos
  rw [← hreal, Matrix.det_mul, Matrix.det_transpose, hz, mul_zero] at h
  exact (lt_irrefl 0) h

theorem real_pair_diagonalization (X Y : Matrix ι ι ℝ) (hX : X.IsSymm) (hY : Y.PosDef) :
    ∃ (L : Matrix ι ι ℝ) (d : ι → ℝ), L.det ≠ 0 ∧
      L.transpose * Y * L = 1 ∧ L.transpose * X * L = Matrix.diagonal d := by
  obtain ⟨P, hP, hPY⟩ := posDef_real_factorization Y hY
  let C := P⁻¹
  have hPC : P * C = 1 := Matrix.mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hP)
  have hCY : C.transpose * Y * C = 1 := by
    rw [← hPY]
    calc
      _ = (P * C).transpose * (P * C) := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hPC, Matrix.transpose_one, one_mul]
  let W := C.transpose * X * C
  have hW : W.IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    change (C.transpose * X * C).transpose = C.transpose * X * C
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hX.eq, Matrix.mul_assoc]
  let U : Matrix ι ι ℝ := hW.eigenvectorUnitary
  have hU : U.transpose * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hW.eigenvectorUnitary
  have hdiag : U.transpose * W * U = Matrix.diagonal hW.eigenvalues := by
    simpa only [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, Function.comp_def, id_eq] using
      hW.conjStarAlgAut_star_eigenvectorUnitary
  refine ⟨C * U, hW.eigenvalues, ?_, ?_, ?_⟩
  · apply Matrix.det_ne_zero_of_left_inverse (A := C * U) (B := U.transpose * P)
    calc
      _ = U.transpose * (P * C) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPC, mul_one, hU]
  · calc
      _ = U.transpose * (C.transpose * Y * C) * U := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hCY, mul_one, hU]
  · calc
      _ = U.transpose * W * U := by simp only [W, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := hdiag

theorem siegel_real_diagonalization (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    ∃ (L : Matrix ι ι ℝ) (d : ι → ℝ), L.det ≠ 0 ∧
      (L.map (algebraMap ℝ ℂ)).transpose * Z.matrix * L.map (algebraMap ℝ ℂ) =
        Matrix.diagonal (fun i => (d i : ℂ) + Complex.I) := by
  let X : Matrix ι ι ℝ := fun i j => (Z.matrix i j).re
  let Y : Matrix ι ι ℝ := fun i j => (Z.matrix i j).im
  obtain ⟨L, d, hL, hY, hX⟩ := real_pair_diagonalization X Y
    (Z.symmetric.map Complex.re) Z.imaginary_posDef
  refine ⟨L, d, hL, ?_⟩
  have hcomplex : Z.matrix = X.map (algebraMap ℝ ℂ) + Complex.I • Y.map (algebraMap ℝ ℂ) := by
    ext i j
    change Z.matrix i j = ((Z.matrix i j).re : ℂ) + Complex.I * ((Z.matrix i j).im : ℂ)
    rw [mul_comm]
    exact (Complex.re_add_im _).symm
  have hXc : (L.map (algebraMap ℝ ℂ)).transpose * X.map (algebraMap ℝ ℂ) * L.map (algebraMap ℝ ℂ) =
      Matrix.diagonal (fun i => (d i : ℂ)) := by
    convert! (show (L.transpose * X * L).map (algebraMap ℝ ℂ) =
        (Matrix.diagonal d).map (algebraMap ℝ ℂ) from
      congrArg (fun A : Matrix ι ι ℝ => A.map (algebraMap ℝ ℂ)) hX) using 1 <;>
      simp only [Matrix.map_mul, ← Matrix.transpose_map, Matrix.diagonal_map, map_zero,
      RCLike.algebraMap_eq_ofReal]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  have hYc : (L.map (algebraMap ℝ ℂ)).transpose * Y.map (algebraMap ℝ ℂ) * L.map (algebraMap ℝ ℂ) = 1 := by
    simpa only [Matrix.map_mul, ← Matrix.transpose_map, Matrix.map_one, map_zero, map_one] using
      congrArg (fun A : Matrix ι ι ℝ => A.map (algebraMap ℝ ℂ)) hY
  rw [hcomplex, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hXc, hYc]
  ext i j
  by_cases hij : i = j <;> simp [hij]

end

end OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction
