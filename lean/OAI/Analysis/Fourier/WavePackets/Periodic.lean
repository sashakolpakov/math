import OAI.Analysis.Fourier.WavePackets.Local

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped ContDiff RealInnerProductSpace

noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Integer frequency vectors in Euclidean coordinates. -/
def integerVector {n : ℕ} (k : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => (k i : ℝ))

theorem integerVector_injective {n : ℕ} : Function.Injective (@integerVector n) := by
  intro k l h
  ext i
  have hi := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) h
  change (k i : ℝ) = (l i : ℝ) at hi
  exact_mod_cast hi

theorem integerVector_mem {n : ℕ} (k : Fin n → ℤ) : integerVector k ∈ integerLattice n := by
  apply ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.mem_span_iff_repr_mem ℤ _).mpr
  intro i
  exact ⟨k i, by simp [integerVector]⟩

noncomputable def integerLatticeEquiv (n : ℕ) : (Fin n → ℤ) ≃ integerLattice n :=
  Equiv.ofBijective (fun k => ⟨integerVector k, integerVector_mem k⟩) (by
    constructor
    · intro k l h
      exact integerVector_injective (congrArg Subtype.val h)
    · intro z
      choose k hk using integerLattice_coordinate z
      refine ⟨k, ?_⟩
      apply Subtype.ext
      ext i
      exact hk i)

/-- Compact symbols meet only finitely many lattice frequencies. -/
theorem finite_support_lattice_sample {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℂ}
    (hs : HasCompactSupport φ) {c : ℝ} (hc : 0 < c) :
    (Function.support (fun k : Fin n → ℤ => φ (c • integerVector k))).Finite := by
  obtain ⟨R, hR, hb⟩ := hs.isBounded.exists_pos_norm_le
  obtain ⟨N, hN⟩ := exists_nat_ge (R / c)
  apply (Set.finite_Icc (fun _ : Fin n => -(N : ℤ)) (fun _ => (N : ℤ))).subset
  intro k hk
  have hsamp : c * ‖integerVector k‖ ≤ R := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hc] using
      hb _ (subset_tsupport φ hk)
  have hnorm : ‖integerVector k‖ ≤ N := le_trans ((le_div_iff₀ hc).mpr (by nlinarith)) hN
  constructor
  · intro i
    have hi : |((k i : ℤ) : ℝ)| ≤ (N : ℝ) := by
      exact le_trans (by simpa [integerVector, Real.norm_eq_abs] using
        PiLp.norm_apply_le (integerVector k) i) hnorm
    exact_mod_cast (abs_le.mp hi).1
  · intro i
    have hi : |((k i : ℤ) : ℝ)| ≤ (N : ℝ) := by
      exact le_trans (by simpa [integerVector, Real.norm_eq_abs] using
        PiLp.norm_apply_le (integerVector k) i) hnorm
    exact_mod_cast (abs_le.mp hi).2

/-- The angular frequencies of the physical torus of side `100`. -/
noncomputable def periodicFrequency {n : ℕ} (k : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  (2 * Real.pi / 100) • integerVector k

noncomputable def periodicSymbol {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (h T : ℝ) (k : Fin n → ℤ) : ℂ :=
  Complex.exp (-Complex.I * ((T * ‖periodicFrequency k‖ : ℝ) : ℂ)) *
    φ (h • periodicFrequency k)

theorem finite_support_periodicSymbol {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℂ}
    (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h) (T : ℝ) :
    (Function.support (periodicSymbol φ h T)).Finite := by
  apply (finite_support_lattice_sample hs (show 0 < h * (2 * Real.pi / 100) by positivity)).subset
  intro k hk
  change periodicSymbol φ h T k ≠ 0 at hk
  change φ ((h * (2 * Real.pi / 100)) • integerVector k) ≠ 0
  contrapose! hk
  simp [periodicSymbol, periodicFrequency, smul_smul, hk]

/-- Kernel relative to physical Lebesgue measure on a fundamental cube of
side `100`. `UnitAddTorus` is used as the coordinate model `x/100`. -/
noncomputable def periodicKernel {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (h T : ℝ) (x : UnitAddTorus (Fin n)) : ℂ :=
  ((100 : ℂ) ^ n)⁻¹ *
    ∑' k : Fin n → ℤ, periodicSymbol φ h T k * UnitAddTorus.mFourier k x

/-- Frequency-localized half-wave on the physical torus of side `100`.
Fourier coefficients use probability Haar measure, cancelling the physical
volume normalization in the convolution formula. -/
noncomputable def periodicHalfWave {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (h T : ℝ) (f : UnitAddTorus (Fin n) → ℂ) (x : UnitAddTorus (Fin n)) : ℂ :=
  ∑' k : Fin n → ℤ, periodicSymbol φ h T k * UnitAddTorus.mFourierCoeff f k *
    UnitAddTorus.mFourier k x

theorem summable_periodicHalfWave {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℂ}
    (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h) (T : ℝ)
    (f : UnitAddTorus (Fin n) → ℂ) (x : UnitAddTorus (Fin n)) :
    Summable (fun k : Fin n → ℤ => periodicSymbol φ h T k *
      UnitAddTorus.mFourierCoeff f k * UnitAddTorus.mFourier k x) := by
  apply summable_of_hasFiniteSupport
  apply (finite_support_periodicSymbol hs hh T).subset
  intro k hk
  contrapose! hk
  simp only [Function.mem_support, not_not] at *
  simp [hk]

theorem mFourier_sub {n : ℕ} (k : Fin n → ℤ) (x y : UnitAddTorus (Fin n)) :
    UnitAddTorus.mFourier k (x - y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier (-k) y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply, Pi.neg_apply,
    fourier_apply, sub_eq_add_neg, zsmul_add, smul_neg, AddCircle.toCircle_add,
    Circle.coe_mul, neg_smul, Finset.prod_mul_distrib]

theorem norm_mFourier_apply {n : ℕ} (k : Fin n → ℤ) (x : UnitAddTorus (Fin n)) :
    ‖UnitAddTorus.mFourier k x‖ = 1 := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply,
    Circle.norm_coe, Finset.prod_const_one]

theorem integrable_mFourier_mul {n : ℕ} {f : UnitAddTorus (Fin n) → ℂ}
    (hf : Integrable f) (k : Fin n → ℤ) :
    Integrable (fun y => UnitAddTorus.mFourier k y * f y) := by
  exact hf.bdd_mul (UnitAddTorus.mFourier k).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => (norm_mFourier_apply k y).le)

theorem integral_mFourier_sub_mul {n : ℕ} (k : Fin n → ℤ)
    (f : UnitAddTorus (Fin n) → ℂ) (x : UnitAddTorus (Fin n)) :
    (∫ y, UnitAddTorus.mFourier k (x - y) * f y) =
      UnitAddTorus.mFourierCoeff f k * UnitAddTorus.mFourier k x := by
  simp_rw [mFourier_sub, mul_assoc]
  rw [integral_const_mul, mul_comm]
  rfl

/-- Fourier multiplication agrees with convolution by the normalized kernel. -/
theorem periodicHalfWave_eq_kernel_integral {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hs : HasCompactSupport φ)
    {h : ℝ} (hh : 0 < h) (T : ℝ) {f : UnitAddTorus (Fin n) → ℂ}
    (hf : Integrable f) (x : UnitAddTorus (Fin n)) :
    periodicHalfWave φ h T f x =
      (100 : ℂ) ^ n * ∫ y, periodicKernel φ h T (x - y) * f y := by
  classical
  let S := (finite_support_periodicSymbol hs hh T).toFinset
  have hS {k : Fin n → ℤ} (hk : k ∉ S) : periodicSymbol φ h T k = 0 := by
    simpa only [S, Set.Finite.mem_toFinset, Function.mem_support, not_not] using hk
  have hkernel (z : UnitAddTorus (Fin n)) :
      (∑' k, periodicSymbol φ h T k * UnitAddTorus.mFourier k z) =
        ∑ k ∈ S, periodicSymbol φ h T k * UnitAddTorus.mFourier k z := by
    apply tsum_eq_sum
    intro k hk
    simp [hS hk]
  have hop : periodicHalfWave φ h T f x =
      ∑ k ∈ S, periodicSymbol φ h T k * UnitAddTorus.mFourierCoeff f k *
        UnitAddTorus.mFourier k x := by
    apply tsum_eq_sum
    intro k hk
    simp [hS hk]
  have hint (k : Fin n → ℤ) : Integrable (fun y =>
      (periodicSymbol φ h T k * UnitAddTorus.mFourier k (x - y)) * f y) := by
    simp_rw [mFourier_sub, mul_assoc]
    exact ((integrable_mFourier_mul hf (-k)).const_mul
      (UnitAddTorus.mFourier k x)).const_mul (periodicSymbol φ h T k)
  rw [hop]
  simp only [periodicKernel, hkernel, mul_assoc]
  rw [integral_const_mul, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero n (by norm_num)), one_mul]
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum S (fun k _ => hint k)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show (fun y => (periodicSymbol φ h T k * UnitAddTorus.mFourier k (x - y)) * f y) =
      (fun y => periodicSymbol φ h T k * (UnitAddTorus.mFourier k (x - y) * f y)) by
    funext y; ring, integral_const_mul, integral_mFourier_sub_mul]

end OAI.Analysis.Fourier.WavePackets
