import OAI.AlgebraicGeometry.ComplexMultiplication.ThetaCompletion
import Mathlib.Analysis.Matrix.Normed

/-! # Theta Covariance -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.ComplexMultiplication.ThetaCovariance.CM

/-!
# The actual first theta coefficient is holomorphic in its period

Differentiation under the covector-valued sum follows from the uniform
Gaussian derivative bound near every positive phase. This sum equals the
actual first Jacobi derivative already constructed. No transformation law
or descent of these local coefficients is assumed here.
-/

open scoped Classical
open Filter _root_.Topology _root_.Metric

variable {V U : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℂ U]

local instance : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℂ) := inferInstance
local instance : NormedSpace ℂ (V →L[ℝ] V →L[ℝ] ℂ) := inferInstance

variable (P : V →L[ℝ] (U →L[ℂ] ℂ)) (L : Submodule ℤ V) (S : Set L)

def thetaPhaseGradientTermOn (x : L) (B : V →L[ℝ] V →L[ℝ] ℂ) : U →L[ℂ] ℂ :=
  if x ∈ S then ThetaCompletion.CM.thetaPhaseGradientTerm P x B else 0

def thetaPhaseGradientTermOnDerivative (x : L) (B : V →L[ℝ] V →L[ℝ] ℂ) :
    (V →L[ℝ] V →L[ℝ] ℂ) →L[ℂ] (U →L[ℂ] ℂ) :=
  if x ∈ S then ThetaCompletion.CM.thetaPhaseGradientTermDerivative P x B else 0

theorem thetaPhaseGradientTermOn_hasFDerivAt (x : L) (B : V →L[ℝ] V →L[ℝ] ℂ) :
    HasFDerivAt (thetaPhaseGradientTermOn P L S x)
      (thetaPhaseGradientTermOnDerivative P L S x B) B := by
  by_cases hx : x ∈ S
  · have heq : thetaPhaseGradientTermOn P L S x = ThetaCompletion.CM.thetaPhaseGradientTerm P x := by
      funext C
      simp only [thetaPhaseGradientTermOn, ite_eq_left hx]
    rw [heq, thetaPhaseGradientTermOnDerivative, ite_eq_left hx]
    exact ThetaCompletion.CM.thetaPhaseGradientTerm_hasFDerivAt P x B
  · have heq : thetaPhaseGradientTermOn P L S x = fun _ => 0 := by
      funext C
      simp only [thetaPhaseGradientTermOn, ite_eq_right hx]
    rw [heq, thetaPhaseGradientTermOnDerivative, ite_eq_right hx]
    exact hasFDerivAt_const (0 : U →L[ℂ] ℂ) B

def thetaPhaseGradientSeriesOn (B : V →L[ℝ] V →L[ℝ] ℂ) : U →L[ℂ] ℂ :=
  ∑' x : L, thetaPhaseGradientTermOn P L S x B

def thetaPhaseGradientSeriesOnDerivative (B : V →L[ℝ] V →L[ℝ] ℂ) :
    (V →L[ℝ] V →L[ℝ] ℂ) →L[ℂ] (U →L[ℂ] ℂ) :=
  ∑' x : L, thetaPhaseGradientTermOnDerivative P L S x B

namespace SiegelPhase

variable [FiniteDimensional ℝ V] [DiscreteTopology L] (Z : CMSiegelPhase.CM.SiegelPhase V)

theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.thetaPhaseGradientTermOn_norm_summable :
    Summable (fun x : L => ‖thetaPhaseGradientTermOn P L S x Z.form‖) := by
  apply (Z.thetaDerivativeMajorant_summable P L 0).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro x
  have heq : thetaPhaseGradientTermOn P L S x Z.form = Z.thetaTermOnDerivative P L S x 0 := by
    simp only [thetaPhaseGradientTermOn, ThetaCompletion.CM.thetaPhaseGradientTerm, CMSiegelPhase.CM.SiegelPhase.thetaTermOnDerivative,
      CMSiegelPhase.CM.SiegelPhase.thetaTermDerivative, Z.thetaTerm_zero, CMSiegelPhase.CM.SiegelPhase.gaussianWeight]
  rw [heq]
  exact Z.thetaTermOnDerivative_norm_le P L S 0 x 0 (by simp)

omit [DiscreteTopology L] in
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.thetaPhaseGradientTermOnDerivative_norm_le (B : V →L[ℝ] V →L[ℝ] ℂ)
    (hB : ‖B - Z.form‖ ≤ Z.lowerBound / 2) (x : L) :
    ‖thetaPhaseGradientTermOnDerivative P L S x B‖ ≤ Z.phaseGradientMajorant P x := by
  unfold thetaPhaseGradientTermOnDerivative
  split_ifs
  · exact Z.thetaPhaseGradientTermDerivative_norm_le P B hB x
  · rw [ContinuousLinearMap.opNorm_zero]
    unfold CMSiegelPhase.CM.SiegelPhase.phaseGradientMajorant
    positivity

theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.thetaPhaseGradientSeriesOn_hasFDerivAt (B : V →L[ℝ] V →L[ℝ] ℂ)
    (hB : ‖B - Z.form‖ < Z.lowerBound / 2) :
    HasFDerivAt (thetaPhaseGradientSeriesOn P L S)
      (thetaPhaseGradientSeriesOnDerivative P L S B) B := by
  exact hasFDerivAt_tsum_of_isPreconnected
    (Z.phaseGradientMajorant_summable P L) isOpen_ball
    (convex_ball Z.form (Z.lowerBound / 2)).isPreconnected
    (fun x C _ => thetaPhaseGradientTermOn_hasFDerivAt P L S x C)
    (fun x C hC => Z.thetaPhaseGradientTermOnDerivative_norm_le P L S C
      (show ‖C - Z.form‖ < Z.lowerBound / 2 by
        simpa only [mem_ball, dist_eq_norm] using hC).le x)
    (mem_ball_self (half_pos Z.lowerBound_pos))
    (Z.thetaPhaseGradientTermOn_norm_summable P L S).of_norm
    (by simpa only [mem_ball, dist_eq_norm] using hB)

/-- Holomorphicity in the ambient complex space of phase coefficients. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.thetaPhaseGradientSeriesOn_differentiableAt :
    DifferentiableAt ℂ (thetaPhaseGradientSeriesOn P L S) Z.form :=
  (Z.thetaPhaseGradientSeriesOn_hasFDerivAt P L S Z.form
    (by simpa only [sub_self, norm_zero] using half_pos Z.lowerBound_pos)).differentiableAt

/-- The holomorphic covector-valued phase series is the actual first
derivative of the original theta series in its Jacobi variable. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.fderiv_thetaSeriesOn_zero_eq_phaseGradientSeries :
    fderiv ℂ (Z.thetaSeriesOn P L S) 0 = thetaPhaseGradientSeriesOn P L S Z.form := by
  rw [Z.fderiv_thetaSeriesOn]
  unfold CMSiegelPhase.CM.SiegelPhase.thetaSeriesOnDerivative thetaPhaseGradientSeriesOn
  apply tsum_congr
  intro x
  simp only [thetaPhaseGradientTermOn, ThetaCompletion.CM.thetaPhaseGradientTerm, CMSiegelPhase.CM.SiegelPhase.thetaTermOnDerivative,
    CMSiegelPhase.CM.SiegelPhase.thetaTermDerivative, Z.thetaTerm_zero, CMSiegelPhase.CM.SiegelPhase.gaussianWeight]

end SiegelPhase

open scoped _root_.Matrix.Norms.Elementwise

variable {ι : Type*} [Fintype ι]

/-- The ordinary matrix coefficients give a complex-linear continuous
parameterization of the corresponding real bilinear phase forms. -/
def thetaMatrixPhaseMap : Matrix ι ι ℂ →L[ℂ] ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ) :=
  (show Matrix ι ι ℂ →ₗ[ℂ] ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ) from
    { toFun := CMSiegelMatrix.CM.siegelMatrixForm
      map_add' := by
        intro A B
        ext x y
        simp [CMSiegelMatrix.CM.siegelMatrixForm_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c A
        ext x y
        change CMSiegelMatrix.CM.siegelMatrixForm (c • A) x y = c * CMSiegelMatrix.CM.siegelMatrixForm A x y
        simp only [CMSiegelMatrix.CM.siegelMatrixForm_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring }).toContinuousLinearMap

theorem thetaMatrixPhaseMap_apply (B : Matrix ι ι ℂ) :
    thetaMatrixPhaseMap B = CMSiegelMatrix.CM.siegelMatrixForm B := rfl

namespace SiegelMatrix

variable (Z : CMSiegelMatrix.CM.SiegelMatrix ι) (S : Set (ThetaCoordinates.CM.thetaCoordinateLattice ι))

/-- The covector-valued first theta coefficient, as a function of the
ordinary complex matrix entries. -/
def _root_.OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.firstThetaCoefficient (B : Matrix ι ι ℂ) : (ι → ℂ) →L[ℂ] ℂ :=
  thetaPhaseGradientSeriesOn (ThetaCoordinates.CM.thetaCoordinatePairing ι) (ThetaCoordinates.CM.thetaCoordinateLattice ι) S
    (CMSiegelMatrix.CM.siegelMatrixForm B)

theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.firstThetaCoefficient_differentiableAt :
    DifferentiableAt ℂ (CMSiegelMatrix.CM.SiegelMatrix.firstThetaCoefficient S) Z.matrix := by
  exact (Z.phase.thetaPhaseGradientSeriesOn_differentiableAt (ThetaCoordinates.CM.thetaCoordinatePairing ι)
    (ThetaCoordinates.CM.thetaCoordinateLattice ι) S).comp Z.matrix
      ((thetaMatrixPhaseMap (ι := ι)).differentiableAt (x := Z.matrix))

theorem _root_.OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.fderiv_completedThetaSeriesOn_zero_eq_firstThetaCoefficient :
    fderiv ℂ (Z.completedThetaSeriesOn S) 0 = CMSiegelMatrix.CM.SiegelMatrix.firstThetaCoefficient S Z.matrix := by
  rw [Z.fderiv_completedThetaSeriesOn_zero]
  exact Z.phase.fderiv_thetaSeriesOn_zero_eq_phaseGradientSeries
    (ThetaCoordinates.CM.thetaCoordinatePairing ι) (ThetaCoordinates.CM.thetaCoordinateLattice ι) S

end SiegelMatrix

end AlgebraicGeometry.ComplexMultiplication.ThetaCovariance.CM

namespace AlgebraicGeometry.ComplexMultiplication

/-!
# Derivatives and completion of a theta functional equation

These are deductions from an explicit functional equation relating two
inputs. They do not assert the Poisson transformation law or silently
identify the transformed input with the original input. The quadratic
factor disappears from the first derivative at zero. A compatible change
of completion removes it from the entire completed expression.
-/

variable {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- First-derivative covariance deduced from the quadratic-exponential
functional equation. The two functions may come from different inputs. -/
theorem ThetaCovariance.CM.theta_first_derivative_covariance
    (A : U →L[ℂ] W) (Q : U →L[ℂ] U →L[ℂ] ℂ) (c : ℂ)
    {f : U → ℂ} {g : W → ℂ} {f' : U →L[ℂ] ℂ} {g' : W →L[ℂ] ℂ}
    (hf : HasFDerivAt f f' 0) (hg : HasFDerivAt g g' 0)
    (htransform : ∀ z, g (A z) = c * (ThetaCompletion.CM.thetaCompletionFactor Q z * f z)) :
    g'.comp A = c • f' := by
  have hleft : HasFDerivAt (fun z => g (A z)) (g'.comp A) 0 := by
    have hgA : HasFDerivAt g g' (A 0) := by simpa only [map_zero] using hg
    exact hgA.comp 0 A.hasFDerivAt
  have hright := (ThetaCompletion.CM.thetaCompletion_mul_hasFDerivAt_zero Q hf).const_smul c
  have heq : (fun z => g (A z)) = fun z => c * (ThetaCompletion.CM.thetaCompletionFactor Q z * f z) :=
    funext htransform
  rw [heq] at hleft
  exact hleft.unique hright

theorem ThetaCovariance.CM.theta_first_derivative_covariance_equiv
    (A : U ≃L[ℂ] W) (Q : U →L[ℂ] U →L[ℂ] ℂ) (c : ℂ)
    {f : U → ℂ} {g : W → ℂ} {f' : U →L[ℂ] ℂ} {g' : W →L[ℂ] ℂ}
    (hf : HasFDerivAt f f' 0) (hg : HasFDerivAt g g' 0)
    (htransform : ∀ z, g (A z) = c * (ThetaCompletion.CM.thetaCompletionFactor Q z * f z)) :
    g' = c • f'.comp A.symm.toContinuousLinearMap := by
  have h := ThetaCovariance.CM.theta_first_derivative_covariance A.toContinuousLinearMap Q c hf hg htransform
  ext w
  have hw := congrArg (fun T : U →L[ℂ] ℂ => T (A.symm w)) h
  simpa using hw

/-- The completion change cancels the quadratic factor pointwise. -/
theorem ThetaCovariance.CM.theta_completion_covariance
    (A : U →L[ℂ] W) (Q : U →L[ℂ] U →L[ℂ] ℂ)
    (Q' : W →L[ℂ] W →L[ℂ] ℂ) (R : U →L[ℂ] U →L[ℂ] ℂ)
    (c : ℂ) (f : U → ℂ) (g : W → ℂ)
    (htransform : ∀ z, g (A z) = c * (ThetaCompletion.CM.thetaCompletionFactor R z * f z))
    (hquadratic : ∀ z, Q' (A z) (A z) + R z z = Q z z) (z : U) :
    ThetaCompletion.CM.thetaCompletionFactor Q' (A z) * g (A z) = c * (ThetaCompletion.CM.thetaCompletionFactor Q z * f z) := by
  rw [htransform]
  unfold ThetaCompletion.CM.thetaCompletionFactor
  calc
    _ = c * ((Complex.exp (Q' (A z) (A z)) * Complex.exp (R z z)) * f z) := by ring
    _ = _ := by rw [← Complex.exp_add, hquadratic]

variable {ι : Type*} [Fintype ι]
  (Z Z' : CMSiegelMatrix.CM.SiegelMatrix ι) (S T : Set (ThetaCoordinates.CM.thetaCoordinateLattice ι))

/-- Covariance of the actual holomorphic first coefficients, provided the
classical functional equation for the two stated inputs. -/
theorem CMSiegelMatrix.CM.SiegelMatrix.firstThetaCoefficient_covariance
    (A : (ι → ℂ) →L[ℂ] (ι → ℂ)) (Q : (ι → ℂ) →L[ℂ] (ι → ℂ) →L[ℂ] ℂ) (c : ℂ)
    (htransform : ∀ z,
      Z'.phase.thetaSeriesOn (ThetaCoordinates.CM.thetaCoordinatePairing ι) (ThetaCoordinates.CM.thetaCoordinateLattice ι) T (A z) =
        c * (ThetaCompletion.CM.thetaCompletionFactor Q z *
          Z.phase.thetaSeriesOn (ThetaCoordinates.CM.thetaCoordinatePairing ι) (ThetaCoordinates.CM.thetaCoordinateLattice ι) S z)) :
    (CMSiegelMatrix.CM.SiegelMatrix.firstThetaCoefficient T Z'.matrix).comp A = c • CMSiegelMatrix.CM.SiegelMatrix.firstThetaCoefficient S Z.matrix := by
  have h := ThetaCovariance.CM.theta_first_derivative_covariance A Q c
    (Z.phase.thetaSeriesOn_hasFDerivAt (ThetaCoordinates.CM.thetaCoordinatePairing ι) (ThetaCoordinates.CM.thetaCoordinateLattice ι) S 0)
    (Z'.phase.thetaSeriesOn_hasFDerivAt (ThetaCoordinates.CM.thetaCoordinatePairing ι) (ThetaCoordinates.CM.thetaCoordinateLattice ι) T 0)
    htransform
  have hf := Z.phase.fderiv_thetaSeriesOn_zero_eq_phaseGradientSeries
    (ThetaCoordinates.CM.thetaCoordinatePairing ι) (ThetaCoordinates.CM.thetaCoordinateLattice ι) S
  have hg := Z'.phase.fderiv_thetaSeriesOn_zero_eq_phaseGradientSeries
    (ThetaCoordinates.CM.thetaCoordinatePairing ι) (ThetaCoordinates.CM.thetaCoordinateLattice ι) T
  rw [Z.phase.fderiv_thetaSeriesOn] at hf
  rw [Z'.phase.fderiv_thetaSeriesOn] at hg
  rwa [hf, hg] at h

end AlgebraicGeometry.ComplexMultiplication

end

end OAI
