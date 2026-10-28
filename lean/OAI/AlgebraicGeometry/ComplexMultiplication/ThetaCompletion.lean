import OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! # Theta Completion -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication

noncomputable section

section

/-!
# Quadratic completion preserves the first theta coefficient

The exponential of any continuous complex bilinear quadratic has value
one and derivative zero at the origin. Consequently multiplication by
the manuscript's explicit inverse-imaginary-matrix Gaussian leaves the
first theta derivative unchanged. This is a calculation at a fixed
Siegel matrix; transformation and descent remain separate obligations.
-/

open scoped Classical _root_.Matrix

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]

def ThetaCompletion.CM.thetaCompletionFactor (Q : U →L[ℂ] U →L[ℂ] ℂ) (z : U) : ℂ := Complex.exp (Q z z)

theorem ThetaCompletion.CM.thetaCompletionFactor_zero (Q : U →L[ℂ] U →L[ℂ] ℂ) :
    ThetaCompletion.CM.thetaCompletionFactor Q 0 = 1 := by simp [ThetaCompletion.CM.thetaCompletionFactor]

theorem ThetaCompletion.CM.thetaCompletionFactor_hasFDerivAt_zero (Q : U →L[ℂ] U →L[ℂ] ℂ) :
    HasFDerivAt (ThetaCompletion.CM.thetaCompletionFactor Q) (0 : U →L[ℂ] ℂ) 0 := by
  have hQ : HasFDerivAt (fun z => Q z z) (0 : U →L[ℂ] ℂ) 0 := by
    simpa using (Q.hasFDerivAt (x := 0)).clm_apply (hasFDerivAt_id (0 : U))
  simpa only [map_zero, zero_apply, Complex.exp_zero, one_smul]
    using! hQ.cexp

/-- A quadratic completion does not change any existing first derivative
at zero, regardless of the constant term of the original function. -/
theorem ThetaCompletion.CM.thetaCompletion_mul_hasFDerivAt_zero (Q : U →L[ℂ] U →L[ℂ] ℂ)
    {f : U → ℂ} {f' : U →L[ℂ] ℂ} (hf : HasFDerivAt f f' 0) :
    HasFDerivAt (fun z => ThetaCompletion.CM.thetaCompletionFactor Q z * f z) f' 0 := by
  convert! (ThetaCompletion.CM.thetaCompletionFactor_hasFDerivAt_zero Q).mul hf using 1
  ext z
  simp [ThetaCompletion.CM.thetaCompletionFactor_zero]

variable {ι : Type*} [Fintype ι] (Z : CMSiegelMatrix.CM.SiegelMatrix ι)

/-- The bilinear form `(π/2) zᵗ (Im Z)⁻¹ w` in the completion.
The explicit `Matrix.inv` selects the matrix inverse instead of the
pointwise inverse instance on the underlying function type. -/
def CMSiegelMatrix.CM.SiegelMatrix.completionForm : (ι → ℂ) →L[ℂ] (ι → ℂ) →L[ℂ] ℂ :=
  ∑ i : ι, ∑ j : ι,
    (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).smulRight
      ((ContinuousLinearMap.proj j : (ι → ℂ) →L[ℂ] ℂ).smulRight
        (((Real.pi : ℂ) / 2) *
          (@Inv.inv (Matrix ι ι ℝ) Matrix.inv (fun i j => (Z.matrix i j).im) i j : ℂ)))

theorem CMSiegelMatrix.CM.SiegelMatrix.completionForm_apply (z w : ι → ℂ) :
    Z.completionForm z w = ((Real.pi : ℂ) / 2) *
      (∑ i, ∑ j, z i *
        (@Inv.inv (Matrix ι ι ℝ) Matrix.inv (fun i j => (Z.matrix i j).im) i j : ℂ) * w j) := by
  simp [CMSiegelMatrix.CM.SiegelMatrix.completionForm, Finset.mul_sum, mul_comm, mul_left_comm]

def CMSiegelMatrix.CM.SiegelMatrix.completedThetaSeriesOn (S : Set (ThetaCoordinates.CM.thetaCoordinateLattice ι)) (z : ι → ℂ) : ℂ :=
  ThetaCompletion.CM.thetaCompletionFactor Z.completionForm z *
    Z.phase.thetaSeriesOn (ThetaCoordinates.CM.thetaCoordinatePairing ι) (ThetaCoordinates.CM.thetaCoordinateLattice ι) S z

theorem CMSiegelMatrix.CM.SiegelMatrix.completedThetaSeriesOn_hasFDerivAt_zero (S : Set (ThetaCoordinates.CM.thetaCoordinateLattice ι)) :
    HasFDerivAt (Z.completedThetaSeriesOn S)
      (Z.phase.thetaSeriesOnDerivative (ThetaCoordinates.CM.thetaCoordinatePairing ι) (ThetaCoordinates.CM.thetaCoordinateLattice ι) S 0)
      0 :=
  ThetaCompletion.CM.thetaCompletion_mul_hasFDerivAt_zero Z.completionForm
    (Z.phase.thetaSeriesOn_hasFDerivAt (ThetaCoordinates.CM.thetaCoordinatePairing ι) (ThetaCoordinates.CM.thetaCoordinateLattice ι) S 0)

theorem CMSiegelMatrix.CM.SiegelMatrix.fderiv_completedThetaSeriesOn_zero (S : Set (ThetaCoordinates.CM.thetaCoordinateLattice ι)) :
    fderiv ℂ (Z.completedThetaSeriesOn S) 0 =
      fderiv ℂ (Z.phase.thetaSeriesOn (ThetaCoordinates.CM.thetaCoordinatePairing ι) (ThetaCoordinates.CM.thetaCoordinateLattice ι) S) 0 := by
  rw [(Z.completedThetaSeriesOn_hasFDerivAt_zero S).fderiv, Z.phase.fderiv_thetaSeriesOn]

/-- The first derivatives of the completed sparse theta functions span the
entire cotangent space, with the actual completion factor included. -/
theorem CMSiegelMatrix.CM.SiegelMatrix.span_completed_sparseThetaGradients_eq_top :
    Submodule.span ℂ (Set.range (fun an : ThetaCoordinates.CM.thetaCoordinateLattice ι × ℕ =>
      fderiv ℂ (Z.completedThetaSeriesOn
        {x | SparseLatticeSums.CM.SparseLatticeCoset (ThetaCoordinates.CM.thetaCoordinateLattice ι) an.2 an.1 x}) 0)) = ⊤ := by
  simpa only [CMSiegelMatrix.CM.SiegelMatrix.fderiv_completedThetaSeriesOn_zero, CMSiegelPhase.CM.SiegelPhase.sparseThetaGradient]
    using Z.span_sparseThetaGradients_eq_top

/-- Linear projection of completed gradients spans exactly the image of
that projection. Identifying the geometric ball projection is separate. -/
theorem CMSiegelMatrix.CM.SiegelMatrix.span_projected_completed_sparseThetaGradients
    {W : Type*} [AddCommGroup W] [Module ℂ W] (P : ((ι → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] W) :
    Submodule.span ℂ (Set.range (fun an : ThetaCoordinates.CM.thetaCoordinateLattice ι × ℕ =>
      P (fderiv ℂ (Z.completedThetaSeriesOn
        {x | SparseLatticeSums.CM.SparseLatticeCoset (ThetaCoordinates.CM.thetaCoordinateLattice ι) an.2 an.1 x}) 0))) =
      LinearMap.range P := by
  rw [Set.range_comp' P, Submodule.span_image, Z.span_completed_sparseThetaGradients_eq_top,
    Submodule.map_top]

end

/-!
# Holomorphic variation of first theta coefficients with the phase

The ambient parameter is the space of continuous complex-valued real
bilinear forms. Evaluation on a fixed real position is complex linear.
Near a positive Siegel phase, a uniform positive Gaussian bound permits
differentiation of the covector-valued first coefficient with respect to
this parameter. The resulting series agrees with the actual Jacobi
derivative at each positive phase.
-/

open scoped Classical
open Filter _root_.Topology _root_.Metric

variable {V U : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℂ U]

-- Name the existing ambient structures before forming complex operator spaces.
local instance ThetaCompletion.CM.phaseParameterNormedAddCommGroup :
    NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℂ) := inferInstance
local instance ThetaCompletion.CM.phaseParameterNormedSpace :
    NormedSpace ℂ (V →L[ℝ] V →L[ℝ] ℂ) := inferInstance

/-- Evaluation of a bilinear phase at `(x,x)` is complex linear in the phase. -/
def ThetaCompletion.CM.thetaPhaseEvaluation (x : V) : (V →L[ℝ] V →L[ℝ] ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    ({ toFun := fun B : V →L[ℝ] V →L[ℝ] ℂ => B x x
       map_add' := by intro B C; simp
       map_smul' := by intro c B; simp } : (V →L[ℝ] V →L[ℝ] ℂ) →ₗ[ℂ] ℂ)
    (‖x‖ ^ 2) (fun B => by
      calc
        ‖B x x‖ ≤ ‖B x‖ * ‖x‖ := (B x).le_opNorm x
        _ ≤ (‖B‖ * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right (B.le_opNorm x) (norm_nonneg x)
        _ = ‖x‖ ^ 2 * ‖B‖ := by ring)

theorem ThetaCompletion.CM.thetaPhaseEvaluation_apply (x : V) (B : V →L[ℝ] V →L[ℝ] ℂ) :
    ThetaCompletion.CM.thetaPhaseEvaluation x B = B x x := rfl

theorem ThetaCompletion.CM.thetaPhaseEvaluation_norm_le (x : V) : ‖ThetaCompletion.CM.thetaPhaseEvaluation x‖ ≤ ‖x‖ ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
  intro B
  change ‖B x x‖ ≤ ‖x‖ ^ 2 * ‖B‖
  calc
    ‖B x x‖ ≤ (‖B‖ * ‖x‖) * ‖x‖ :=
      ((B x).le_opNorm x).trans (mul_le_mul_of_nonneg_right (B.le_opNorm x) (norm_nonneg x))
    _ = _ := by ring

def ThetaCompletion.CM.thetaPhaseGradientTerm (P : V →L[ℝ] (U →L[ℂ] ℂ)) (x : V)
    (B : V →L[ℝ] V →L[ℝ] ℂ) : U →L[ℂ] ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * B x x) •
    ((2 * (Real.pi : ℂ) * Complex.I) • P x)

def ThetaCompletion.CM.thetaPhaseGradientTermDerivative (P : V →L[ℝ] (U →L[ℂ] ℂ)) (x : V)
    (B : V →L[ℝ] V →L[ℝ] ℂ) : (V →L[ℝ] V →L[ℝ] ℂ) →L[ℂ] (U →L[ℂ] ℂ) :=
  (Complex.exp ((Real.pi : ℂ) * Complex.I * B x x) •
    (((Real.pi : ℂ) * Complex.I) • ThetaCompletion.CM.thetaPhaseEvaluation x)).smulRight
    ((2 * (Real.pi : ℂ) * Complex.I) • P x)

theorem ThetaCompletion.CM.thetaPhaseGradientTerm_hasFDerivAt (P : V →L[ℝ] (U →L[ℂ] ℂ)) (x : V)
    (B : V →L[ℝ] V →L[ℝ] ℂ) :
    HasFDerivAt (ThetaCompletion.CM.thetaPhaseGradientTerm P x) (ThetaCompletion.CM.thetaPhaseGradientTermDerivative P x B) B := by
  have h := ((ThetaCompletion.CM.thetaPhaseEvaluation x).hasFDerivAt (x := B)).const_smul
    ((Real.pi : ℂ) * Complex.I)
  exact h.cexp.smul_const ((2 * (Real.pi : ℂ) * Complex.I) • P x)

variable [FiniteDimensional ℝ V] (Z : CMSiegelPhase.CM.SiegelPhase V)
  (P : V →L[ℝ] (U →L[ℂ] ℂ))

theorem CMSiegelPhase.CM.SiegelPhase.nearby_phase_imaginary_lower_bound (B : V →L[ℝ] V →L[ℝ] ℂ)
    (hB : ‖B - Z.form‖ ≤ Z.lowerBound / 2) (x : V) :
    (Z.lowerBound / 2) * ‖x‖ ^ 2 ≤ (B x x).im := by
  have heval : ‖(B - Z.form) x x‖ ≤ (Z.lowerBound / 2) * ‖x‖ ^ 2 := by
    calc
      ‖(B - Z.form) x x‖ ≤ ‖ThetaCompletion.CM.thetaPhaseEvaluation x‖ * ‖B - Z.form‖ :=
        (ThetaCompletion.CM.thetaPhaseEvaluation x).le_opNorm (B - Z.form)
      _ ≤ ‖x‖ ^ 2 * (Z.lowerBound / 2) :=
        mul_le_mul (ThetaCompletion.CM.thetaPhaseEvaluation_norm_le x) hB (norm_nonneg _) (sq_nonneg _)
      _ = _ := mul_comm _ _
  have him := (neg_le_abs ((B - Z.form) x x).im).trans
    ((Complex.abs_im_le_norm _).trans heval)
  simp only [sub_apply, Complex.sub_im] at him
  have hZ := Z.imaginaryQuadratic_lower_bound x
  change Z.lowerBound * ‖x‖ ^ 2 ≤ (Z.form x x).im at hZ
  nlinarith

theorem CMSiegelPhase.CM.SiegelPhase.nearby_phase_gaussian_bound (B : V →L[ℝ] V →L[ℝ] ℂ)
    (hB : ‖B - Z.form‖ ≤ Z.lowerBound / 2) (x : V) :
    ‖Complex.exp ((Real.pi : ℂ) * Complex.I * B x x)‖ ≤
      Real.exp (-(Real.pi * (Z.lowerBound / 2)) * ‖x‖ ^ 2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (Z.nearby_phase_imaginary_lower_bound B hB x)
    Real.pi_pos.le
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  nlinarith

def CMSiegelPhase.CM.SiegelPhase.phaseGradientMajorant (x : V) : ℝ :=
  (2 * Real.pi ^ 2 * ‖P‖) *
    (‖x‖ ^ 3 * Real.exp (-(Real.pi * (Z.lowerBound / 2)) * ‖x‖ ^ 2))

theorem CMSiegelPhase.CM.SiegelPhase.phaseGradientMajorant_summable (L : Submodule ℤ V) [DiscreteTopology L] :
    Summable (fun x : L => Z.phaseGradientMajorant P x) := by
  simpa only [CMSiegelPhase.CM.SiegelPhase.phaseGradientMajorant, zero_mul, add_zero] using!
    (LatticeGaussian.CM.lattice_gaussian_poly_summable L (Real.pi * (Z.lowerBound / 2)) 0
      (mul_pos Real.pi_pos (half_pos Z.lowerBound_pos)) 3).mul_left (2 * Real.pi ^ 2 * ‖P‖)

theorem CMSiegelPhase.CM.SiegelPhase.thetaPhaseGradientTermDerivative_norm_le (B : V →L[ℝ] V →L[ℝ] ℂ)
    (hB : ‖B - Z.form‖ ≤ Z.lowerBound / 2) (x : V) :
    ‖ThetaCompletion.CM.thetaPhaseGradientTermDerivative P x B‖ ≤ Z.phaseGradientMajorant P x := by
  have hc : ‖(Real.pi : ℂ) * Complex.I‖ = Real.pi := by simp
  have hc2 : ‖2 * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by simp
  rw [ThetaCompletion.CM.thetaPhaseGradientTermDerivative, ContinuousLinearMap.norm_smulRight_apply,
    norm_smul, norm_smul, norm_smul, hc, hc2]
  calc
    _ ≤ (Real.exp (-(Real.pi * (Z.lowerBound / 2)) * ‖x‖ ^ 2) *
        (Real.pi * ‖x‖ ^ 2)) * (2 * Real.pi * (‖P‖ * ‖x‖)) := by
      gcongr
      · exact Z.nearby_phase_gaussian_bound B hB x
      · exact ThetaCompletion.CM.thetaPhaseEvaluation_norm_le x
      · exact P.le_opNorm x
    _ = _ := by unfold CMSiegelPhase.CM.SiegelPhase.phaseGradientMajorant; ring

end

end OAI.AlgebraicGeometry.ComplexMultiplication
