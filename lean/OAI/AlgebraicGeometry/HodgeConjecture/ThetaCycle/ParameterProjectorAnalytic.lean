import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoordinateProjector

/-! # Parameter Projector Analytic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ParameterProjectorAnalytic.CM

noncomputable section

/-! ThetaCycle: an actual analytic parameter family for the total projection matrices. -/

open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

theorem fixed_distinguished_projection_holomorphic
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] (β : ℂ) (w : HeckeCycles.GeometricSource.CM.Vec ℂ × HeckeCycles.GeometricSource.CM.Vec ℂ) :
    Differentiable ℂ (fun q : P × HeckeCycles.GeometricSource.CM.BallChart =>
      (CompactComplex.CM.ballLineProjection q.2 w.1, CompactComplex.CM.ballAnnihilatorProjection β q.2 w.2)) := by
  apply Differentiable.prodMk
  · apply differentiable_pi.mpr
    intro j
    fin_cases j <;> simp [CompactComplex.CM.ballLineProjection, HeckeCycles.GeometricSource.CM.BallDatum.lineVector] <;> fun_prop
  · apply differentiable_pi.mpr
    intro j
    fin_cases j <;> simp [CompactComplex.CM.ballAnnihilatorProjection, div_eq_mul_inv]
    fun_prop

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]

local instance totalAmbientNormedAddCommGroup : NormedAddCommGroup (ComplexTransition.CM.TotalAmbient K) :=
  inferInstanceAs (NormedAddCommGroup (Fin 2 → Gal(K/ℚ) → Fin 3 → ℂ))

local instance totalAmbientNormedSpace : NormedSpace ℂ (ComplexTransition.CM.TotalAmbient K) :=
  inferInstanceAs (NormedSpace ℂ (Fin 2 → Gal(K/ℚ) → Fin 3 → ℂ))

abbrev CompactParameters (places : HeckeCycles.GeometricSource.CM.Places K) := Fin places.count → Analysis.DifferentialForms.Coordinates.LocalApproximation.CompactPeriod

theorem parameter_projector_value_joint_holomorphic (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (w : ComplexTransition.CM.TotalAmbient K) (i : Fin 2) (τ : Fin places.count) :
    Differentiable ℂ (fun q : CompactParameters K places × HeckeCycles.GeometricSource.CM.BallChart =>
      ProjectorParameters.CM.parameterProjectorValue K B places q.1 q.2 w i τ) := by
  by_cases hτ : τ = places.distinguished
  · simp only [ProjectorParameters.CM.parameterProjectorValue, ite_eq_left hτ]
    change Differentiable ℂ (fun q : CompactParameters K places × HeckeCycles.GeometricSource.CM.BallChart =>
      (CompactComplex.CM.ballLineProjection q.2 (Symplectic.CM.galoisToPaired K places (w i) τ).1,
        CompactComplex.CM.ballAnnihilatorProjection (B.b : ℂ) q.2 (Symplectic.CM.galoisToPaired K places (w i) τ).2))
    exact fixed_distinguished_projection_holomorphic (B.b : ℂ) (Symplectic.CM.galoisToPaired K places (w i) τ)
  · simp only [ProjectorParameters.CM.parameterProjectorValue, ite_eq_right hτ]
    apply Differentiable.prodMk
    all_goals
      apply differentiable_pi.mpr
      intro j
      simp only [Matrix.mulVec, dotProduct]
      fun_prop

def parameterAmbientProjection (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (p : CompactParameters K places) (z : HeckeCycles.GeometricSource.CM.BallChart) (w : ComplexTransition.CM.TotalAmbient K) : ComplexTransition.CM.TotalAmbient K :=
  fun i => (Symplectic.CM.galoisToPaired K places).symm
    (fun τ => ProjectorParameters.CM.parameterProjectorValue K B places p z w i τ)

theorem parameter_ambient_projection_joint_holomorphic (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (w : ComplexTransition.CM.TotalAmbient K) :
    Differentiable ℂ (fun q : CompactParameters K places × HeckeCycles.GeometricSource.CM.BallChart =>
      parameterAmbientProjection K B places q.1 q.2 w) := by
  apply differentiable_pi.mpr
  intro i
  exact (Symplectic.CM.galoisToPaired K places).symm.toContinuousLinearEquiv.differentiable.comp
    (differentiable_pi.mpr (fun τ => parameter_projector_value_joint_holomorphic K B places w i τ))

variable {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase)

theorem parameter_ambient_projection_approximation {ε : ℝ}
    (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (w : ComplexTransition.CM.TotalAmbient K) :
    parameterAmbientProjection K D.ball D.places (ApproximationSequence.CM.newCompactPeriods K D A) z w =
      TotalProjector.CM.approximationProjector K D A z w := by
  funext i
  apply (Symplectic.CM.galoisToPaired K D.places).injective
  change Symplectic.CM.galoisToPaired K D.places ((Symplectic.CM.galoisToPaired K D.places).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  funext τ
  exact (ProjectorParameters.CM.approximation_projector_parameter_value K D A z w i τ).symm

theorem parameter_ambient_projection_original (z : HeckeCycles.GeometricSource.CM.BallChart) (w : ComplexTransition.CM.TotalAmbient K) :
    parameterAmbientProjection K D.ball D.places (ApproximationSequence.CM.oldCompactPeriods K D) z w =
      TotalProjector.CM.totalSourceProjector K D.ball D.places (FourSplittings.CM.initialThetaSigns K v) z w := by
  funext i
  apply (Symplectic.CM.galoisToPaired K D.places).injective
  change Symplectic.CM.galoisToPaired K D.places ((Symplectic.CM.galoisToPaired K D.places).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  funext τ
  exact (ProjectorParameters.CM.original_projector_parameter_value K D z w i τ).symm

def parameterCoordinateProjector (p : CompactParameters K D.places) (z : HeckeCycles.GeometricSource.CM.BallChart) :
    Matrix (Sum (PeriodTotal.CM.TotalPositions K D.places) (PeriodTotal.CM.TotalPositions K D.places))
      (Sum (PeriodTotal.CM.TotalPositions K D.places) (PeriodTotal.CM.TotalPositions K D.places)) ℂ :=
  fun i j => ComplexTransition.CM.totalComplexCoordinates K (fun k => (D.initialPeriods k).coordinates)
    (parameterAmbientProjection K D.ball D.places p z
      ((ComplexTransition.CM.totalComplexCoordinates K (fun k => (D.initialPeriods k).coordinates)).symm (Pi.single j 1))) i

theorem parameter_coordinate_projector_joint_holomorphic :
    Differentiable ℂ (fun q : CompactParameters K D.places × HeckeCycles.GeometricSource.CM.BallChart =>
      parameterCoordinateProjector K D q.1 q.2) := by
  apply differentiable_pi.mpr
  intro i
  apply differentiable_pi.mpr
  intro j
  exact (differentiable_apply i).comp
    ((ComplexTransition.CM.totalComplexCoordinates K (fun k => (D.initialPeriods k).coordinates)).toContinuousLinearEquiv.differentiable.comp
      (parameter_ambient_projection_joint_holomorphic K D.ball D.places _))

theorem parameter_coordinate_projector_approximation {ε : ℝ}
    (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε) (z : HeckeCycles.GeometricSource.CM.BallChart) :
    parameterCoordinateProjector K D (ApproximationSequence.CM.newCompactPeriods K D A) z =
      CoordinateProjector.CM.coordinateProjector K (fun i => (D.initialPeriods i).coordinates) (TotalProjector.CM.approximationProjector K D A z) := by
  ext i j
  change ComplexTransition.CM.totalComplexCoordinates K (fun k => (D.initialPeriods k).coordinates)
    (parameterAmbientProjection K D.ball D.places (ApproximationSequence.CM.newCompactPeriods K D A) z _) i = _
  rw [parameter_ambient_projection_approximation]
  rfl

theorem parameter_coordinate_projector_original (z : HeckeCycles.GeometricSource.CM.BallChart) :
    parameterCoordinateProjector K D (ApproximationSequence.CM.oldCompactPeriods K D) z =
      CoordinateProjector.CM.coordinateProjector K (fun i => (D.initialPeriods i).coordinates)
        (TotalProjector.CM.totalSourceProjector K D.ball D.places (FourSplittings.CM.initialThetaSigns K v) z) := by
  ext i j
  change ComplexTransition.CM.totalComplexCoordinates K (fun k => (D.initialPeriods k).coordinates)
    (parameterAmbientProjection K D.ball D.places (ApproximationSequence.CM.oldCompactPeriods K D) z _) i = _
  rw [parameter_ambient_projection_original]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ParameterProjectorAnalytic.CM
