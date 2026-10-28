import OAI.RepresentationTheory.Theta.Adelic.GaussianSchwartz
import OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson

/-! # Siegel Gaussian -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SiegelGaussian.CM

noncomputable section

/-! ThetaCycle: construct the full Siegel Gaussian as an actual Schwartz map.
The standard vacuum is constructed explicitly; no Weil-data package is
assumed to supply it. -/

open scoped Classical
open OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction
open OAI.RepresentationTheory.Theta.Adelic.GaussianSchwartz

variable (I : Type*) [Fintype I]

def euclideanVacuumExponent (x : EuclideanSpace ℝ I) : ℂ :=
  -((∑ i, (x i) ^ 2 : ℝ) : ℂ)

theorem euclidean_vacuum_exponent_temperate :
    Function.HasTemperateGrowth (euclideanVacuumExponent I) := by
  have hc (i : I) : Function.HasTemperateGrowth (fun x : EuclideanSpace ℝ I => x i) :=
    (EuclideanSpace.proj i).hasTemperateGrowth
  exact (Complex.ofRealCLM.hasTemperateGrowth.comp
    (.sum fun i _ => (hc i).pow 2)).neg

theorem euclidean_vacuum_exponent_re (x : EuclideanSpace ℝ I) :
    (euclideanVacuumExponent I x).re = -‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

def euclideanVacuumSchwartz : SchwartzMap (EuclideanSpace ℝ I) ℂ :=
  RepresentationTheory.Theta.Adelic.GaussianSchwartz.gaussianOfExponent (euclideanVacuumExponent I) (euclidean_vacuum_exponent_temperate I)
    (euclidean_vacuum_exponent_re I)

def coordinateVacuumSchwartz : SchwartzMap (I → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv I ℝ).symm
    (euclideanVacuumSchwartz I)

theorem coordinate_vacuum_schwartz_apply (x : I → ℝ) :
    coordinateVacuumSchwartz I x = Complex.exp (-((∑ i, (x i) ^ 2 : ℝ) : ℂ)) := rfl

def standardVacuumSchwartz : SchwartzMap (I → ℝ) ℂ :=
  RepresentationTheory.Theta.RealPoisson.AutomorphyConstruction.scaledRealSchwartz (Real.sqrt Real.pi) (Real.sqrt_pos.mpr Real.pi_pos).ne'
    (coordinateVacuumSchwartz I)

theorem standard_vacuum_schwartz_apply (x : I → ℝ) :
    standardVacuumSchwartz I x =
      Complex.exp (-((Real.pi * ∑ i, (x i) ^ 2 : ℝ) : ℂ)) := by
  rw [standardVacuumSchwartz, RepresentationTheory.Theta.RealPoisson.AutomorphyConstruction.scaledRealSchwartz_apply, coordinate_vacuum_schwartz_apply]
  have h : (∑ i, (Real.sqrt Real.pi * x i) ^ 2) = Real.pi * ∑ i, (x i) ^ 2 := by
    simp only [mul_pow, ← Finset.mul_sum, Real.sq_sqrt Real.pi_pos.le]
  exact congrArg (fun r : ℝ => Complex.exp (-(r : ℂ))) h

theorem scaled_standard_vacuum_apply (r : ℝ) (hr : r ≠ 0) (x : I → ℝ) :
    RepresentationTheory.Theta.RealPoisson.AutomorphyConstruction.scaledRealSchwartz r hr (standardVacuumSchwartz I) x = Complex.exp (-RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.radialExponent r x) := by
  rw [RepresentationTheory.Theta.RealPoisson.AutomorphyConstruction.scaledRealSchwartz_apply, standard_vacuum_schwartz_apply]
  congr 1
  change -((Real.pi * ∑ i, (r * x i) ^ 2 : ℝ) : ℂ) =
    -((Real.pi * r ^ 2 * ∑ i, (x i) ^ 2 : ℝ) : ℂ)
  simp only [mul_pow, ← Finset.mul_sum, mul_assoc]

variable {I}

def siegelGaussianSchwartz (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (z : I → ℂ) : SchwartzMap (I → ℝ) ℂ :=
  SchwartzMap.smulLeftCLM ℂ
    (fun x => Complex.exp (RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianExponent Z z x + RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.radialExponent (RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianDamping Z) x))
    (RepresentationTheory.Theta.RealPoisson.AutomorphyConstruction.scaledRealSchwartz (RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianDamping Z) (RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianDamping_pos Z).ne' (standardVacuumSchwartz I))

theorem siegel_gaussian_schwartz_apply (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (z : I → ℂ) (x : I → ℝ) :
    siegelGaussianSchwartz Z z x = RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction Z z x := by
  rw [siegelGaussianSchwartz, SchwartzMap.smulLeftCLM_apply_apply (RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianRemainder_temperate Z z),
    smul_eq_mul, scaled_standard_vacuum_apply, ← Complex.exp_add]
  unfold RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction
  congr 1
  ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SiegelGaussian.CM
