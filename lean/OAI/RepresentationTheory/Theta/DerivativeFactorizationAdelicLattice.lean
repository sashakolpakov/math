import OAI.RepresentationTheory.Theta.DerivativeFactorizationDefinitions

/-! # Derivative Factorization Adelic Lattice -/

namespace OAI.RepresentationTheory.Theta.DerivativeFactorizationAdelicLattice

noncomputable section

section

/-! Compact finite-adelic supports have a common integral denominator. -/

open scoped Classical
open IsDedekindDomain Filter

abbrev Prime := HeightOneSpectrum ℤ

def IntegralAdeles (a : DerivativeFactorizationDefinitions.AQf) : Prop :=
  ∀ v : Prime, a v ∈ v.adicCompletionIntegers ℚ

theorem integralAdeles_open : IsOpen {a : DerivativeFactorizationDefinitions.AQf | IntegralAdeles a} := by
  exact RestrictedProduct.isOpen_forall_mem
    (fun v : Prime => Valued.isOpen_valuationSubring (v.adicCompletion ℚ))

theorem integralAdeles_intCast (n : ℤ) : IntegralAdeles (n : DerivativeFactorizationDefinitions.AQf) := by
  intro v
  change (n : v.adicCompletion ℚ) ∈ _
  simp

theorem integralAdeles_mul {a b : DerivativeFactorizationDefinitions.AQf}
    (ha : IntegralAdeles a) (hb : IntegralAdeles b) :
    IntegralAdeles (a * b) := by
  intro v
  exact (v.adicCompletionIntegers ℚ).toSubring.mul_mem (ha v) (hb v)

theorem integralAdeles_mul_of_dvd {d e : ℤ} (h : d ∣ e)
    {a : DerivativeFactorizationDefinitions.AQf} (ha : IntegralAdeles ((d : DerivativeFactorizationDefinitions.AQf) * a)) :
    IntegralAdeles ((e : DerivativeFactorizationDefinitions.AQf) * a) := by
  obtain ⟨k, rfl⟩ := h
  simpa only [Int.cast_mul, mul_assoc, mul_left_comm] using
    integralAdeles_mul (integralAdeles_intCast k) ha

theorem exists_integral_denominator (a : DerivativeFactorizationDefinitions.AQf) :
    ∃ d : ℤ, d ≠ 0 ∧ IntegralAdeles ((d : DerivativeFactorizationDefinitions.AQf) * a) := by
  let S : Finset Prime := (show {v : Prime | a v ∉ v.adicCompletionIntegers ℚ}.Finite from a.2).toFinset
  have hS (v : Prime) : v ∉ S → a v ∈ v.adicCompletionIntegers ℚ := by
    simpa only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using
      (show ¬ (a v ∉ v.adicCompletionIntegers ℚ) →
        a v ∈ v.adicCompletionIntegers ℚ from not_not.mp)
  have localDen (v : Prime) : ∃ d : ℤ, d ≠ 0 ∧
      a v * (d : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
    obtain ⟨d, hd, hi⟩ :=
      HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (a v)
    exact ⟨d, nonZeroDivisors.ne_zero hd, by simpa using hi⟩
  choose d hd hi using localDen
  refine ⟨∏ v ∈ S, d v, Finset.prod_ne_zero_iff.mpr (fun v _ =>
    hd v), ?_⟩
  intro v
  by_cases hv : v ∈ S
  · have hdvd : d v ∣ ∏ w ∈ S, d w := Finset.dvd_prod_of_mem d hv
    obtain ⟨k, hk⟩ := hdvd
    rw [hk]
    change ((d v * k : ℤ) : v.adicCompletion ℚ) * a v ∈ _
    rw [Int.cast_mul, mul_right_comm, mul_comm (d v : v.adicCompletion ℚ)]
    exact (v.adicCompletionIntegers ℚ).toSubring.mul_mem (hi v)
      (by simp)
  · change ((∏ w ∈ S, d w : ℤ) : v.adicCompletion ℚ) * a v ∈ _
    exact (v.adicCompletionIntegers ℚ).toSubring.mul_mem
      (intCast_mem (v.adicCompletionIntegers ℚ).toSubring _)
      (hS v hv)

theorem compact_integral_denominator {K : Set DerivativeFactorizationDefinitions.AQf} (hK : IsCompact K) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ a ∈ K, IntegralAdeles ((d : DerivativeFactorizationDefinitions.AQf) * a) := by
  let U (d : {d : ℤ // d ≠ 0}) : Set DerivativeFactorizationDefinitions.AQf :=
    {a | IntegralAdeles ((d.1 : DerivativeFactorizationDefinitions.AQf) * a)}
  have hU (d : {d : ℤ // d ≠ 0}) : IsOpen (U d) :=
    integralAdeles_open.preimage (continuous_const.mul continuous_id)
  have hcover : K ⊆ ⋃ d, U d := by
    intro a _
    obtain ⟨d, hd, ha⟩ := exists_integral_denominator a
    exact Set.mem_iUnion.mpr ⟨⟨d, hd⟩, ha⟩
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover U hU hcover
  refine ⟨∏ d ∈ S, d.1,
    Finset.prod_ne_zero_iff.mpr (fun d _ => d.2), ?_⟩
  intro a ha
  obtain ⟨d, hd, had⟩ := Set.mem_iUnion₂.mp (hS ha)
  exact integralAdeles_mul_of_dvd (Finset.dvd_prod_of_mem _ hd) had

theorem integralAdeles_rat (q : ℚ)
    (hq : IntegralAdeles (algebraMap ℚ DerivativeFactorizationDefinitions.AQf q)) :
    ∃ n : ℤ, (n : ℚ) = q := by
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one (R := ℤ) ℚ q
  intro v
  have hv := hq v
  simpa only [FiniteAdeleRing.algebraMap_apply,
    HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using hv

theorem input_common_denominator {ι : Type*} [Fintype ι] (φ : DerivativeFactorizationDefinitions.Input ι) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ x : ι → ℚ, φ.1 (DerivativeFactorizationDefinitions.diagonal x) ≠ 0 →
      ∀ i, ∃ n : ℤ, (n : ℚ) = d * x i := by
  have hc (i : ι) : IsCompact ((fun a : ι → DerivativeFactorizationDefinitions.AQf => a i) '' tsupport φ.1) :=
    φ.2.2.image (continuous_apply i)
  choose d hd hi using fun i : ι => compact_integral_denominator (hc i)
  refine ⟨∏ i, d i, Finset.prod_ne_zero_iff.mpr (fun i _ => hd i), ?_⟩
  intro x hx i
  have hm : DerivativeFactorizationDefinitions.diagonal x i ∈ (fun a : ι → DerivativeFactorizationDefinitions.AQf => a i) '' tsupport φ.1 :=
    ⟨DerivativeFactorizationDefinitions.diagonal x, subset_tsupport φ.1 hx, rfl⟩
  have h := integralAdeles_mul_of_dvd
    (Finset.dvd_prod_of_mem d (Finset.mem_univ i)) (hi i _ hm)
  apply integralAdeles_rat
  simpa only [map_mul, map_intCast, DerivativeFactorizationDefinitions.diagonal] using h

end

section

/-! Rational theta sums represented by bounded inputs on discrete lattices. -/

open scoped Classical BoundedContinuousFunction CompactlySupported

variable {ι : Type*} [Fintype ι]

def denominatorLattice (d : ℤ) : Submodule ℤ (ι → ℝ) :=
  ZLattice.comap ℝ (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι)
    ((d : ℝ) • (LinearMap.id : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)))

theorem denominatorLattice_discrete {d : ℤ} (hd : d ≠ 0) :
    DiscreteTopology (denominatorLattice (ι := ι) d) := by
  apply ZLattice.comap_discreteTopology ℝ (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinateLattice ι)
  · exact continuous_const.smul continuous_id
  · intro x y h
    exact (smul_right_injective (M := ι → ℝ) (by exact_mod_cast hd : (d : ℝ) ≠ 0)) h

theorem mem_denominatorLattice (d : ℤ) (x : ι → ℝ) :
    x ∈ denominatorLattice d ↔ ∀ i, ∃ n : ℤ, (n : ℝ) = (d : ℝ) * x i := by
  change (d : ℝ) • x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) ↔ _
  exact (Pi.basisFun ℝ ι).mem_span_iff_repr_mem ℤ ((d : ℝ) • x)

def latticePosition {d : ℤ} (x : denominatorLattice (ι := ι) d) : ι → ℚ :=
  fun i => ((mem_denominatorLattice d x).mp x.2 i).choose / d

theorem realPosition_latticePosition {d : ℤ} (hd : d ≠ 0)
    (x : denominatorLattice (ι := ι) d) :
    DerivativeFactorizationDefinitions.realPosition (latticePosition x) = (x : ι → ℝ) := by
  ext i
  have hi := ((mem_denominatorLattice d x).mp x.2 i).choose_spec
  simp only [DerivativeFactorizationDefinitions.realPosition, latticePosition, Rat.cast_div, Rat.cast_intCast]
  rw [hi]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast hd : (d : ℝ) ≠ 0)

theorem latticePosition_injective {d : ℤ} (hd : d ≠ 0) :
    Function.Injective (latticePosition (ι := ι) (d := d)) := by
  intro x y h
  apply Subtype.ext
  simpa only [realPosition_latticePosition hd] using congrArg DerivativeFactorizationDefinitions.realPosition h

def boundedInput (φ : DerivativeFactorizationDefinitions.Input ι) : (ι → DerivativeFactorizationDefinitions.AQf) →ᵇ ℂ :=
  (show C_c(ι → DerivativeFactorizationDefinitions.AQf, ℂ) from
    { toFun := φ.1
      continuous_toFun := φ.2.1.continuous
      hasCompactSupport' := φ.2.2 }).toBoundedContinuousFunction

def latticeInput {d : ℤ} (hd : d ≠ 0) (φ : DerivativeFactorizationDefinitions.Input ι) :
    denominatorLattice (ι := ι) d →ᵇ ℂ :=
  letI := denominatorLattice_discrete (ι := ι) hd
  (boundedInput φ).compContinuous
    ⟨fun x => DerivativeFactorizationDefinitions.diagonal (latticePosition x), continuous_of_discreteTopology⟩

theorem latticeInput_apply {d : ℤ} (hd : d ≠ 0) (φ : DerivativeFactorizationDefinitions.Input ι)
    (x : denominatorLattice (ι := ι) d) :
    latticeInput hd φ x = φ.1 (DerivativeFactorizationDefinitions.diagonal (latticePosition x)) := rfl

omit [Fintype ι] in
theorem realPosition_injective : Function.Injective (DerivativeFactorizationDefinitions.realPosition (ι := ι)) := by
  intro x y h
  ext i
  exact Rat.cast_injective (congrFun h i : (x i : ℝ) = (y i : ℝ))

theorem mem_range_latticePosition {d : ℤ} (hd : d ≠ 0) (x : ι → ℚ)
    (hx : ∀ i, ∃ n : ℤ, (n : ℚ) = d * x i) :
    x ∈ Set.range (latticePosition (ι := ι) (d := d)) := by
  have hm : DerivativeFactorizationDefinitions.realPosition x ∈ denominatorLattice d := by
    rw [mem_denominatorLattice]
    intro i
    obtain ⟨n, hn⟩ := hx i
    refine ⟨n, ?_⟩
    change (n : ℝ) = (d : ℝ) * (x i : ℝ)
    exact_mod_cast hn
  refine ⟨⟨DerivativeFactorizationDefinitions.realPosition x, hm⟩, ?_⟩
  apply realPosition_injective
  exact realPosition_latticePosition hd _

theorem tsum_latticeInput {d : ℤ} (hd : d ≠ 0) (φ : DerivativeFactorizationDefinitions.Input ι)
    (hsupp : ∀ x : ι → ℚ, φ.1 (DerivativeFactorizationDefinitions.diagonal x) ≠ 0 →
      ∀ i, ∃ n : ℤ, (n : ℚ) = d * x i)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (f : (ι → ℝ) → Y) :
    (∑' x : ι → ℚ, φ.1 (DerivativeFactorizationDefinitions.diagonal x) • f (DerivativeFactorizationDefinitions.realPosition x)) =
      ∑' x : denominatorLattice (ι := ι) d, latticeInput hd φ x • f x := by
  symm
  have h := (latticePosition_injective (ι := ι) hd).tsum_eq
    (f := fun x : ι → ℚ => φ.1 (DerivativeFactorizationDefinitions.diagonal x) • f (DerivativeFactorizationDefinitions.realPosition x))
    (fun x hx => mem_range_latticePosition hd x
      (hsupp x (fun hz => hx (by simp [hz]))))
  simpa only [latticeInput_apply, realPosition_latticePosition hd] using h

theorem theta_eq_weighted {d : ℤ} (hd : d ≠ 0) (φ : DerivativeFactorizationDefinitions.Input ι)
    (hsupp : ∀ x : ι → ℚ, φ.1 (DerivativeFactorizationDefinitions.diagonal x) ≠ 0 →
      ∀ i, ∃ n : ℤ, (n : ℚ) = d * x i)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    DerivativeFactorizationDefinitions.theta φ Z.matrix z =
      Z.phase.weightedThetaSeries (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι)
        (denominatorLattice d) (latticeInput hd φ) z := by
  simpa only [DerivativeFactorizationDefinitions.theta, DerivativeFactorizationDefinitions.kernel, AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.weightedThetaSeries,
    AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.weightedThetaTerm, AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.thetaTerm, AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.phase,
    smul_eq_mul] using
    tsum_latticeInput hd φ hsupp (fun x => Z.phase.thetaTerm (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι) x z)

theorem firstCoefficient_eq_weighted {d : ℤ} (hd : d ≠ 0) (φ : DerivativeFactorizationDefinitions.Input ι)
    (hsupp : ∀ x : ι → ℚ, φ.1 (DerivativeFactorizationDefinitions.diagonal x) ≠ 0 →
      ∀ i, ∃ n : ℤ, (n : ℚ) = d * x i)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    DerivativeFactorizationDefinitions.firstCoefficient φ Z.matrix =
      Z.phase.weightedThetaSeriesDerivative (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι)
        (denominatorLattice d) (latticeInput hd φ) 0 := by
  have h := tsum_latticeInput hd φ hsupp
    (fun x => AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaPhaseGradientTerm (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι) x
      (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z.matrix))
  simpa only [DerivativeFactorizationDefinitions.firstCoefficient, AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.weightedThetaSeriesDerivative,
    AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.weightedThetaTermDerivative, AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.thetaTermDerivative,
    AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaPhaseGradientTerm, AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.thetaTerm_zero,
    AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.gaussianWeight, AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.phase] using h

theorem theta_norm_summable (φ : DerivativeFactorizationDefinitions.Input ι) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    Summable (fun x : ι → ℚ => ‖φ.1 (DerivativeFactorizationDefinitions.diagonal x) * DerivativeFactorizationDefinitions.kernel Z.matrix x z‖) := by
  obtain ⟨d, hd, hsupp⟩ := input_common_denominator φ
  let := denominatorLattice_discrete (ι := ι) hd
  apply ((latticePosition_injective (ι := ι) hd).summable_iff
    (f := fun x : ι → ℚ => ‖φ.1 (DerivativeFactorizationDefinitions.diagonal x) * DerivativeFactorizationDefinitions.kernel Z.matrix x z‖) ?_).mp
  · simpa only [Function.comp_def, DerivativeFactorizationDefinitions.kernel, realPosition_latticePosition hd,
      AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.weightedThetaTerm, latticeInput_apply,
      AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.thetaTerm, AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.phase] using
      Z.phase.weightedThetaTerm_norm_summable (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι)
        (denominatorLattice d) (latticeInput hd φ) z
  · intro x hx
    have hzero : φ.1 (DerivativeFactorizationDefinitions.diagonal x) = 0 := by
      by_contra hn
      exact hx (mem_range_latticePosition hd x (hsupp x hn))
    simp [hzero]

end

/-! First coefficients of finite-adelic theta inputs are holomorphic. -/

open scoped Classical BoundedContinuousFunction _root_.Matrix.Norms.Elementwise
open _root_.Metric

section Weighted
variable {V U : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℂ U]

local instance : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℂ) := inferInstance
local instance : NormedSpace ℂ (V →L[ℝ] V →L[ℝ] ℂ) := inferInstance

def weightedFirst (P : V →L[ℝ] (U →L[ℂ] ℂ))
    (L : Submodule ℤ V) (φ : L →ᵇ ℂ)
    (B : V →L[ℝ] V →L[ℝ] ℂ) : U →L[ℂ] ℂ :=
  ∑' x : L, φ x • AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaPhaseGradientTerm P x B

theorem weightedFirst_differentiableAt
    [FiniteDimensional ℝ V]
    (P : V →L[ℝ] (U →L[ℂ] ℂ))
    (L : Submodule ℤ V) [DiscreteTopology L]
    (φ : L →ᵇ ℂ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase V) :
    DifferentiableAt ℂ (weightedFirst P L φ) Z.form := by
  have hs : Summable (fun x : L => ‖φ‖ * Z.phaseGradientMajorant P x) :=
    (Z.phaseGradientMajorant_summable P L).mul_left ‖φ‖
  have hbase : Summable (fun x : L => φ x • AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaPhaseGradientTerm P x Z.form) := by
    simpa only [AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaPhaseGradientTerm, AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.weightedThetaTermDerivative,
      AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.thetaTermDerivative, AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.thetaTerm_zero,
      AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.gaussianWeight] using
      (Z.weightedThetaTermDerivative_norm_summable P L φ 0).of_norm
  apply HasFDerivAt.differentiableAt
    (f' := ∑' x : L, φ x • AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaPhaseGradientTermDerivative P x Z.form)
  apply hasFDerivAt_tsum_of_isPreconnected hs isOpen_ball
    (convex_ball Z.form (Z.lowerBound / 2)).isPreconnected
    (fun x B _ => (AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaPhaseGradientTerm_hasFDerivAt P x B).const_smul (φ x))
    _ (mem_ball_self (half_pos Z.lowerBound_pos)) hbase
    (mem_ball_self (half_pos Z.lowerBound_pos))
  intro x B hB
  rw [norm_smul]
  exact mul_le_mul (φ.norm_coe_le_norm x)
    (Z.thetaPhaseGradientTermDerivative_norm_le P B
      (show ‖B - Z.form‖ < Z.lowerBound / 2 by
        simpa only [mem_ball, dist_eq_norm] using hB).le x)
    (norm_nonneg _) (norm_nonneg _)

end Weighted

variable {ι : Type*} [Fintype ι]

local instance coordinatePhaseNormedAddCommGroup :
    NormedAddCommGroup ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ) := inferInstance
local instance coordinatePhaseNormedSpace :
    NormedSpace ℂ ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ) := inferInstance

theorem theta_hasFDerivAt_zero (φ : DerivativeFactorizationDefinitions.Input ι) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    HasFDerivAt (DerivativeFactorizationDefinitions.theta φ Z.matrix) (DerivativeFactorizationDefinitions.firstCoefficient φ Z.matrix) 0 := by
  obtain ⟨d, hd, hsupp⟩ := input_common_denominator φ
  let := denominatorLattice_discrete (ι := ι) hd
  rw [firstCoefficient_eq_weighted hd φ hsupp Z]
  have heq := funext (theta_eq_weighted hd φ hsupp Z)
  rw [heq]
  exact Z.phase.weightedThetaSeries_hasFDerivAt (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι)
    (denominatorLattice d) (latticeInput hd φ) 0

theorem firstCoefficient_differentiableAt (φ : DerivativeFactorizationDefinitions.Input ι) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    DifferentiableAt ℂ (DerivativeFactorizationDefinitions.firstCoefficient φ) Z.matrix := by
  obtain ⟨d, hd, hsupp⟩ := input_common_denominator φ
  let := denominatorLattice_discrete (ι := ι) hd
  have heq : DerivativeFactorizationDefinitions.firstCoefficient φ = fun B =>
      weightedFirst (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι) (denominatorLattice d)
        (latticeInput hd φ) (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm B) := by
    funext B
    exact tsum_latticeInput hd φ hsupp
      (fun x => AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaPhaseGradientTerm (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι) x (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm B))
  rw [heq]
  let T : Matrix ι ι ℂ →L[ℂ] ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ) :=
    (AlgebraicGeometry.ComplexMultiplication.ThetaCovariance.CM.thetaMatrixPhaseMap (ι := ι)).toLinearMap.toContinuousLinearMap
  exact (weightedFirst_differentiableAt (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι)
    (denominatorLattice d) (latticeInput hd φ) Z.phase).comp Z.matrix
    (T.differentiableAt (x := Z.matrix))

theorem first_derivatives_uncorrected_holomorphic
    (φ : DerivativeFactorizationDefinitions.Input ι) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    HasFDerivAt (DerivativeFactorizationDefinitions.theta φ Z.matrix) (DerivativeFactorizationDefinitions.firstCoefficient φ Z.matrix) 0 ∧
    HasFDerivAt (DerivativeFactorizationDefinitions.completed φ Z) (DerivativeFactorizationDefinitions.firstCoefficient φ Z.matrix) 0 ∧
    fderiv ℂ (DerivativeFactorizationDefinitions.completed φ Z) 0 = fderiv ℂ (DerivativeFactorizationDefinitions.theta φ Z.matrix) 0 ∧
    DifferentiableAt ℂ (DerivativeFactorizationDefinitions.firstCoefficient φ) Z.matrix := by
  have h := theta_hasFDerivAt_zero φ Z
  have hc := AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletion_mul_hasFDerivAt_zero Z.completionForm h
  exact ⟨h, hc, hc.fderiv.trans h.fderiv.symm, firstCoefficient_differentiableAt φ Z⟩

end

end OAI.RepresentationTheory.Theta.DerivativeFactorizationAdelicLattice
