import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
import OAI.RepresentationTheory.Theta.Adelic.GaussianSchwartz

/-! # Vacuum -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Vacuum.CM

noncomputable section

/-! Construct PoissonAutomorphy's standard real Gaussian vacuum directly as a
Schwartz function. Its existence is independent of any Weil data. -/

open scoped Classical
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

variable (I : Type*) [Fintype I]

def exponent (x : EuclideanSpace ℝ I) : ℂ := -∑ i, (x i : ℂ) ^ 2

theorem exponent_temperate : Function.HasTemperateGrowth (exponent I) := by
  have hc (i : I) : Function.HasTemperateGrowth (fun x : EuclideanSpace ℝ I => (x i : ℂ)) :=
    (Complex.ofRealCLM.comp ((ContinuousLinearMap.proj i : (I → ℝ) →L[ℝ] ℝ).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)).toContinuousLinearMap)).hasTemperateGrowth
  exact (Function.HasTemperateGrowth.sum (fun i _ => (hc i).pow 2)).neg

theorem exponent_real (x : EuclideanSpace ℝ I) : (exponent I x).re = -‖x‖ ^ 2 := by
  simp only [exponent, ← Complex.ofReal_pow, Complex.neg_re, Complex.re_sum,
    Complex.ofReal_re, EuclideanSpace.real_norm_sq_eq]

def euclideanGaussian : SchwartzMap (EuclideanSpace ℝ I) ℂ :=
  RepresentationTheory.Theta.Adelic.GaussianSchwartz.gaussianOfExponent (exponent I)
    (exponent_temperate I) (exponent_real I)

def gaussianCoordinates : (I → ℝ) ≃L[ℝ] EuclideanSpace ℝ I :=
  ((LinearEquiv.smulOfNeZero ℝ (I → ℝ) (Real.sqrt Real.pi)
    (Real.sqrt_pos.mpr Real.pi_pos).ne').toContinuousLinearEquiv).trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)).symm

def gaussian : SchwartzMap (I → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (gaussianCoordinates I) (euclideanGaussian I)

theorem gaussian_apply (x : I → ℝ) :
    gaussian I x = Complex.exp (-((Real.pi : ℂ) * ∑ i, (x i : ℂ) ^ 2)) := by
  change Complex.exp (-∑ i, (((Real.sqrt Real.pi) * x i : ℝ) : ℂ) ^ 2) = _
  congr 1
  simp only [Complex.ofReal_mul, mul_pow, ← Finset.mul_sum,
    ← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]

def vacuum : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I :=
  ⟨gaussian I, Submodule.subset_span ⟨gaussian I, rfl⟩⟩

theorem vacuum_apply (x : I → ℝ) :
    (vacuum I).val x = Complex.exp (-((Real.pi : ℂ) * ∑ i, (x i : ℂ) ^ 2)) :=
  gaussian_apply I x

theorem vacuum_zero : (vacuum I).val 0 = 1 := by
  simp only [vacuum_apply, Pi.zero_apply, Complex.ofReal_zero, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, mul_zero, neg_zero, Complex.exp_zero]

theorem vacuum_ne_zero : vacuum I ≠ 0 := by
  intro h
  have he := congrArg (fun f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I => f.val 0) h
  rw [vacuum_zero] at he
  exact one_ne_zero he

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.Vacuum.CM
