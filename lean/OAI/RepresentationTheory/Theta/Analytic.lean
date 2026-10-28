import OAI.RepresentationTheory.Theta.Definitions
import OAI.RepresentationTheory.Theta.AnalyticSeries

/-! # Analytic -/

namespace OAI.RepresentationTheory.Theta.Analytic

noncomputable section

/-! Gaussian bounds give joint analyticity in the phase and Jacobi variables. -/

open scoped Classical BigOperators _root_.Topology NNReal ENNReal BoundedContinuousFunction _root_.Matrix.Norms.Elementwise

section Phase
variable {V U : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℂ U]

abbrev PhaseParameter (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  V →L[ℝ] V →L[ℝ] ℂ

local instance phaseParameterNormedAddCommGroup :
    NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℂ) := inferInstance
local instance phaseParameterNormedSpace :
    NormedSpace ℂ (V →L[ℝ] V →L[ℝ] ℂ) := inferInstance

def phaseExponent (P : V →L[ℝ] (U →L[ℂ] ℂ)) (x : V) :
    (PhaseParameter V × U) →L[ℂ] ℂ :=
  ((Real.pi : ℂ) * Complex.I) •
      ((AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaPhaseEvaluation x).comp (ContinuousLinearMap.fst ℂ _ _)) +
    (2 * (Real.pi : ℂ) * Complex.I) •
      ((P x).comp (ContinuousLinearMap.snd ℂ _ _))

theorem phaseExponent_apply (P : V →L[ℝ] (U →L[ℂ] ℂ)) (x : V)
    (w : PhaseParameter V × U) :
    phaseExponent P x w =
      (Real.pi : ℂ) * Complex.I * w.1 x x +
        (2 * (Real.pi : ℂ) * Complex.I) * P x w.2 := rfl

theorem phaseExponent_norm_le (P : V →L[ℝ] (U →L[ℂ] ℂ)) (x : V) :
    ‖phaseExponent P x‖ ≤ Real.pi * ‖x‖ ^ 2 + 2 * Real.pi * ‖P‖ * ‖x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [phaseExponent_apply]
  have hb : ‖w.1 x x‖ ≤ ‖x‖ ^ 2 * ‖w‖ := by
    calc
      ‖w.1 x x‖ ≤ ‖AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaPhaseEvaluation x‖ * ‖w.1‖ :=
        (AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaPhaseEvaluation x).le_opNorm w.1
      _ ≤ ‖x‖ ^ 2 * ‖w‖ := by
        gcongr
        · exact AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaPhaseEvaluation_norm_le x
        · exact norm_fst_le w
  have hp : ‖P x w.2‖ ≤ ‖P‖ * ‖x‖ * ‖w‖ :=
    (AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.pairing_norm_le P x w.2).trans
      (mul_le_mul_of_nonneg_left (norm_snd_le w) (by positivity))
  calc
    _ ≤ ‖(Real.pi : ℂ) * Complex.I * w.1 x x‖ +
        ‖(2 * (Real.pi : ℂ) * Complex.I) * P x w.2‖ := norm_add_le _ _
    _ = Real.pi * ‖w.1 x x‖ + (2 * Real.pi) * ‖P x w.2‖ := by
      simp [abs_of_pos Real.pi_pos]
    _ ≤ Real.pi * (‖x‖ ^ 2 * ‖w‖) +
        (2 * Real.pi) * (‖P‖ * ‖x‖ * ‖w‖) := by gcongr
    _ = _ := by ring

variable [FiniteDimensional ℝ V]

theorem phase_theta_analytic
    (L : Submodule ℤ V) [DiscreteTopology L] (φ : L →ᵇ ℂ)
    (P : V →L[ℝ] (U →L[ℂ] ℂ)) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase V) (z : U) :
    AnalyticAt ℂ
      (fun w : PhaseParameter V × U =>
        ∑' x : L, φ x * Complex.exp (phaseExponent P x w)) (Z.form, z) := by
  let r : ℝ≥0 := ⟨Z.lowerBound / 2, (half_pos Z.lowerBound_pos).le⟩
  apply AnalyticSeries.analyticAt_exponential_sum (fun x : L => φ x)
    (fun x : L => phaseExponent P x) (Z.form, z) r (half_pos Z.lowerBound_pos)
  have hsum := (AlgebraicGeometry.ComplexMultiplication.LatticeGaussian.CM.lattice_gaussian_summable L
    (Real.pi * (Z.lowerBound / 2))
    (2 * Real.pi * ‖P‖ * (‖z‖ + (r : ℝ)))
    (mul_pos Real.pi_pos (half_pos Z.lowerBound_pos))).mul_left ‖φ‖
  apply hsum.of_nonneg_of_le (fun _ => by positivity)
  intro x
  have htheta : ‖Complex.exp (phaseExponent P (x : V) (Z.form, z))‖ ≤
      Z.thetaMajorant P ‖z‖ x :=
    Z.thetaTerm_norm_le P ‖z‖ x z le_rfl
  have hexp : Real.exp (‖phaseExponent P (x : V)‖ * (r : ℝ)) ≤
      Real.exp ((Real.pi * ‖(x : V)‖ ^ 2 + 2 * Real.pi * ‖P‖ * ‖(x : V)‖) *
        (r : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (phaseExponent_norm_le P x) r.coe_nonneg)
  rw [norm_mul]
  calc
    _ ≤ (‖φ‖ * Z.thetaMajorant P ‖z‖ x) *
        Real.exp ((Real.pi * ‖(x : V)‖ ^ 2 + 2 * Real.pi * ‖P‖ * ‖(x : V)‖) *
          (r : ℝ)) := by
      apply mul_le_mul
      · exact mul_le_mul (φ.norm_coe_le_norm x) htheta
          (norm_nonneg _) (norm_nonneg _)
      · exact hexp
      · exact (Real.exp_pos _).le
      · exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
    _ = ‖φ‖ * Real.exp
        (-(Real.pi * (Z.lowerBound / 2)) * ‖(x : V)‖ ^ 2 +
          (2 * Real.pi * ‖P‖ * (‖z‖ + (r : ℝ))) * ‖(x : V)‖) := by
      unfold AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.thetaMajorant
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      change -(Real.pi * Z.lowerBound) * ‖(x : V)‖ ^ 2 +
          (2 * Real.pi * ‖P‖ * ‖z‖) * ‖(x : V)‖ +
          (Real.pi * ‖(x : V)‖ ^ 2 + 2 * Real.pi * ‖P‖ * ‖(x : V)‖) *
            (Z.lowerBound / 2) = _
      change _ = -(Real.pi * (Z.lowerBound / 2)) * ‖(x : V)‖ ^ 2 +
        (2 * Real.pi * ‖P‖ * (‖z‖ + Z.lowerBound / 2)) * ‖(x : V)‖
      ring

end Phase

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance coordinatePhaseNormedAddCommGroup :
    NormedAddCommGroup ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ) := inferInstance
local instance coordinatePhaseNormedSpace :
    NormedSpace ℂ ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ) := inferInstance

def coordinatePhaseMap : Matrix ι ι ℂ →L[ℂ]
    ((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ) :=
  (AlgebraicGeometry.ComplexMultiplication.ThetaCovariance.CM.thetaMatrixPhaseMap (ι := ι)).toLinearMap.toContinuousLinearMap

omit [DecidableEq ι] in
theorem theta_joint_analytic
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] (φ : L →ᵇ ℂ)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    AnalyticAt ℂ (fun w : Matrix ι ι ℂ × (ι → ℂ) => Definitions.theta L φ w.1 w.2)
      (Z.matrix, z) := by
  let T : (Matrix ι ι ℂ × (ι → ℂ)) →L[ℂ]
      (((ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℂ) × (ι → ℂ)) :=
    coordinatePhaseMap.prodMap (ContinuousLinearMap.id ℂ (ι → ℂ))
  have h := phase_theta_analytic L φ (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι) Z.phase z
  have hc : AnalyticAt ℂ T (Z.matrix, z) := T.analyticAt _
  have h' : AnalyticAt ℂ
      (fun w : PhaseParameter (ι → ℝ) × (ι → ℂ) =>
        ∑' x : L, φ x * Complex.exp (phaseExponent (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι) x w))
      (T (Z.matrix, z)) := h
  have hh := h'.comp (f := T) hc
  convert hh using 1
  funext w
  simp only [Function.comp_apply, Definitions.theta, phaseExponent_apply,
    AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing_apply]
  rfl

end

end OAI.RepresentationTheory.Theta.Analytic
