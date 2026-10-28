import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FourierSeriesUniqueness
import OAI.RepresentationTheory.Theta.Geometric.LinearTheta
import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier
import OAI.RepresentationTheory.Theta.FiniteSupport

/-! # Fourier -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Fourier.CM.Coefficients

/-! The bounded denominator of an actual finite Schwartz support gives
integer-indexed theta coefficients. Their absolute summability follows
from theta convergence, and they determine the entire finite input. -/

open scoped Classical
open OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction

variable {I : Type} [Fintype I]

def frequency (N : ℕ) (n : I → ℤ) : I → ℚ := fun i => (n i : ℚ) / (N : ℚ)

omit [Fintype I] in
theorem frequency_injective (N : ℕ) (hN : 0 < N) : Function.Injective (frequency (I := I) N) := by
  intro n m h
  funext i
  have hn : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hi := congrFun h i
  change (n i : ℚ) / (N : ℚ) = (m i : ℚ) / (N : ℚ) at hi
  have he := (div_left_inj' hn).mp hi
  exact_mod_cast he

omit [Fintype I] in
theorem frequency_range (N : ℕ) (hN : 0 < N) (x : I → ℚ)
    (hx : ∀ i, ∃ m : ℤ, (m : ℚ) = (N : ℚ) * x i) : x ∈ Set.range (frequency (I := I) N) := by
  choose n hn using hx
  refine ⟨n, ?_⟩
  funext i
  change (n i : ℚ) / (N : ℚ) = x i
  rw [hn]
  exact mul_div_cancel_left₀ (x i) (by exact_mod_cast hN.ne')

def coefficient (N : ℕ) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (n : I → ℤ) : ℂ :=
  RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm φ Z 0 (frequency N n)

theorem coefficient_norm_summable (N : ℕ) (hN : 0 < N) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) :
    Summable (fun n => ‖coefficient N φ Z n‖) :=
  (RepresentationTheory.Theta.Geometric.LinearTheta.theta_terms_summable φ Z 0).norm.comp_injective (frequency_injective N hN)

theorem coefficient_zero_iff (N : ℕ) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (n : I → ℤ) :
    coefficient N φ Z n = 0 ↔ φ.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (frequency N n)) = 0 := by
  change _ * Complex.exp _ = 0 ↔ _
  exact mul_eq_zero.trans (or_iff_left (Complex.exp_ne_zero _))

theorem input_zero (N : ℕ) (hN : 0 < N) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I)
    (hden : ∀ x : I → ℚ, φ.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x) ≠ 0 → ∀ i, ∃ m : ℤ, (m : ℚ) = (N : ℚ) * x i)
    (hc : ∀ n : I → ℤ, coefficient N φ Z n = 0) : φ = 0 := by
  apply Subtype.ext
  apply RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.denseRange_finiteDiagonal.equalizer (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_continuous φ) continuous_zero
  funext x
  change φ.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x) = 0
  by_contra hx
  obtain ⟨n, hn⟩ := frequency_range N hN x (hden x hx)
  have hzero := (coefficient_zero_iff N φ Z n).mp (hc n)
  rw [hn] at hzero
  exact hx hzero

theorem support_coefficients_determine (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I)
    (hc : ∀ n : I → ℤ, coefficient (RepresentationTheory.Theta.FiniteSupport.supportDenominator φ) φ Z n = 0) : φ = 0 :=
  input_zero (RepresentationTheory.Theta.FiniteSupport.supportDenominator φ) (RepresentationTheory.Theta.FiniteSupport.supportDenominator_spec φ).1 φ Z
    (RepresentationTheory.Theta.FiniteSupport.supportDenominator_spec φ).2 hc

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Fourier.CM.Coefficients

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Fourier.CM.Terms

/-! On a scaled real Jacobi variable each actual theta term is its
Gaussian coefficient times the corresponding torus Fourier monomial. -/

open scoped Classical
open UnitAddTorus
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Fourier.CM.Coefficients

variable {I : Type} [Fintype I]

def projection (x : I → ℝ) : UnitAddTorus I := fun i => (x i : UnitAddCircle)

theorem monomial (n : I → ℤ) (x : I → ℝ) :
    mFourier n (projection x) =
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (n i : ℂ) * (x i : ℂ)) := by
  simp only [mFourier, ContinuousMap.coe_mk, projection, fourier_coe_apply,
    Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem linear_phase (N : ℕ) (hN : 0 < N) (n : I → ℤ) (x : I → ℝ) :
    (∑ i, (Coefficients.frequency N n i : ℂ) * ((N : ℂ) * (x i : ℂ))) = ∑ i, (n i : ℂ) * (x i : ℂ) := by
  apply Finset.sum_congr rfl
  intro i _
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Coefficients.frequency, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  field_simp

theorem term (N : ℕ) (hN : 0 < N) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I)
    (n : I → ℤ) (x : I → ℝ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm φ Z (fun i => (N : ℂ) * (x i : ℂ)) (Coefficients.frequency N n) =
      Coefficients.coefficient N φ Z n * mFourier n (projection x) := by
  simp only [Coefficients.coefficient, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  rw [linear_phase N hN, monomial, Complex.exp_add]
  exact (mul_assoc _ _ _).symm

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Fourier.CM.Terms

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Fourier.CM.Injectivity

/-! At any positive Siegel period the full theta function determines its
actual finite Schwartz input. Recover its Fourier coefficients on the
bounded-denominator torus and then use density of rational finite adeles. -/

open scoped Classical
open UnitAddTorus
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Fourier.CM.Coefficients OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Fourier.CM.Terms

variable {I : Type} [Fintype I]

omit [Fintype I] in
theorem projection_surjective : Function.Surjective (Terms.projection (I := I)) := by
  intro t
  have h : ∀ i, ∃ x : ℝ, (x : UnitAddCircle) = t i := fun i => QuotientAddGroup.mk_surjective (t i)
  choose x hx using h
  exact ⟨x, funext hx⟩

def series (N : ℕ) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) : C(UnitAddTorus I, ℂ) :=
  ∑' n : I → ℤ, Coefficients.coefficient N φ Z n • mFourier n

theorem series_value (N : ℕ) (hN : 0 < N) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I)
    (hden : ∀ x : I → ℚ, φ.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x) ≠ 0 → ∀ i, ∃ m : ℤ, (m : ℚ) = (N : ℚ) * x i)
    (x : I → ℝ) : series N φ Z (Terms.projection x) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta φ Z (fun i => (N : ℂ) * (x i : ℂ)) := by
  have hs := (ContinuousMap.evalCLM ℂ (Terms.projection x)).hasSum
    (FourierSeriesUniqueness.CM.summable (Coefficients.coefficient_norm_summable N hN φ Z)).hasSum
  have hsupport : Function.support (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm φ Z (fun i => (N : ℂ) * (x i : ℂ))) ⊆
      Set.range (Coefficients.frequency (I := I) N) := by
    intro q hq
    apply Coefficients.frequency_range N hN q
    apply hden q
    intro hz
    apply hq
    simp only [RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm, hz, zero_mul]
  calc
    series N φ Z (Terms.projection x) =
      ∑' n : I → ℤ, Coefficients.coefficient N φ Z n * mFourier n (Terms.projection x) := hs.tsum_eq.symm
    _ = ∑' n : I → ℤ, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm φ Z (fun i => (N : ℂ) * (x i : ℂ)) (Coefficients.frequency N n) :=
      tsum_congr (fun n => (Terms.term N hN φ Z n x).symm)
    _ = _ := (Coefficients.frequency_injective N hN).tsum_eq hsupport

theorem input_zero (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I)
    (h : ∀ z : I → ℂ, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta φ Z z = 0) : φ = 0 := by
  let N := RepresentationTheory.Theta.FiniteSupport.supportDenominator φ
  have hN : 0 < N := (RepresentationTheory.Theta.FiniteSupport.supportDenominator_spec φ).1
  have hden := (RepresentationTheory.Theta.FiniteSupport.supportDenominator_spec φ).2
  have hf : series N φ Z = 0 := by
    ext t
    obtain ⟨x, rfl⟩ := projection_surjective t
    rw [series_value N hN φ Z hden x, h]
    rfl
  have hs := (FourierSeriesUniqueness.CM.summable (Coefficients.coefficient_norm_summable N hN φ Z)).hasSum
  change HasSum (fun n => Coefficients.coefficient N φ Z n • mFourier n) (series N φ Z) at hs
  rw [hf] at hs
  have hz : HasSum (fun n : I → ℤ => (0 : ℂ) • mFourier n) (0 : C(UnitAddTorus I, ℂ)) := by
    have he : (fun n : I → ℤ => (0 : ℂ) • mFourier n) =
        fun _ : I → ℤ => (0 : C(UnitAddTorus I, ℂ)) := funext (fun n => zero_smul ℂ (mFourier n))
    rw [he]
    exact hasSum_zero
  have hc := FourierSeriesUniqueness.CM.coefficients_eq hs hz
  exact Coefficients.input_zero N hN φ Z hden (fun n => congrFun hc n)

theorem injective (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) : Function.Injective (fun φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I =>
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta φ Z) := by
  intro φ ψ h
  apply sub_eq_zero.mp
  apply input_zero (φ - ψ) Z
  intro z
  change RepresentationTheory.Theta.Geometric.LinearTheta.scalarThetaLinear Z (φ - ψ) z = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (congrFun h z)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Fourier.CM.Injectivity

end

end OAI
