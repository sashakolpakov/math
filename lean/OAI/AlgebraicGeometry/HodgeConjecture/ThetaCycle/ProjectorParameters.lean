import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntertwiningBasis
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ApproximationSequence

/-! # Projector Parameters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ProjectorParameters.CM

noncomputable section

/-! ThetaCycle: the actual total projectors depend continuously on the compact
period data, independently of the chosen rational basis coordinates. -/

open scoped Classical _root_.Matrix _root_.Topology _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open _root_.Module Filter

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]

def parameterProjectorValue (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (p : Fin places.count → Analysis.DifferentialForms.Coordinates.LocalApproximation.CompactPeriod) (z : HeckeCycles.GeometricSource.CM.BallChart) (w : ComplexTransition.CM.TotalAmbient K)
    (i : Fin 2) (τ : Fin places.count) : HeckeCycles.GeometricSource.CM.Vec ℂ × HeckeCycles.GeometricSource.CM.Vec ℂ :=
  if τ = places.distinguished then CompactComplex.CM.distinguishedProjection K B z (Symplectic.CM.galoisToPaired K places (w i) τ)
  else (fun j => ((p τ).1 *ᵥ (fun k => (Symplectic.CM.galoisToPaired K places (w k) τ).1 j)) i,
    fun j => ((p τ).2 *ᵥ (fun k => (Symplectic.CM.galoisToPaired K places (w k) τ).2 j)) i)

theorem parameter_projector_value_continuous (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (w : ComplexTransition.CM.TotalAmbient K) (i : Fin 2) (τ : Fin places.count) :
    Continuous (fun p => parameterProjectorValue K B places p z w i τ) := by
  by_cases hτ : τ = places.distinguished
  · simp only [parameterProjectorValue, ite_eq_left hτ]
    exact continuous_const
  · simp only [parameterProjectorValue, ite_eq_right hτ]
    apply Continuous.prodMk <;> apply continuous_pi <;> intro j <;>
      simp only [Matrix.mulVec, dotProduct] <;> fun_prop

omit [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K] in
theorem complex_standard_basis_change (w : ComplexTransition.CM.TotalAmbient K) :
    ComplexTransition.CM.complexTensorBasisChange K (Pi.basisFun K (Fin 2)) w = w := by
  funext i τ j
  fin_cases i <;> simp [ComplexTransition.CM.complexTensorBasisChange]

variable {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase)

theorem approximation_projector_parameter_value {ε : ℝ}
    (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (w : ComplexTransition.CM.TotalAmbient K) (i : Fin 2) (τ : Fin D.places.count) :
    Symplectic.CM.galoisToPaired K D.places (TotalProjector.CM.approximationProjector K D A z w i) τ =
      parameterProjectorValue K D.ball D.places (ApproximationSequence.CM.newCompactPeriods K D A) z w i τ := by
  obtain ⟨x, rfl⟩ := (CompactComplex.CM.complexTensorBasisEquiv K A.basis).surjective w
  have hleft : TotalProjector.CM.approximationProjector K D A z (CompactComplex.CM.complexTensorBasisEquiv K A.basis x) =
      ComplexTransition.CM.complexTensorBasisChange K A.basis
        (TotalProjector.CM.totalSourceProjector K D.ball D.places (FourSplittings.CM.newThetaSigns K v) z x) := by
    change CompactComplex.CM.complexTensorBasisEquiv K A.basis
      (TotalProjector.CM.totalSourceProjector K D.ball D.places (FourSplittings.CM.newThetaSigns K v) z
        ((CompactComplex.CM.complexTensorBasisEquiv K A.basis).symm (CompactComplex.CM.complexTensorBasisEquiv K A.basis x))) = _
    rw [LinearEquiv.symm_apply_apply, CompactComplex.CM.complex_tensor_basis_equiv_apply]
  rw [hleft, CompactComplex.CM.complex_tensor_basis_equiv_apply]
  by_cases hτ : τ = D.places.distinguished
  · subst τ
    simp only [parameterProjectorValue, ite_true]
    exact IntertwiningBasis.CM.distinguished_projector_intertwines K D.ball D.places (FourSplittings.CM.newThetaSigns K v) A.basis z x i
  · simp only [parameterProjectorValue, ite_eq_right hτ]
    apply Prod.ext <;> funext j
    · exact IntertwiningBasis.CM.compact_projector_intertwines_first K D.ball D.places (FourSplittings.CM.newThetaSigns K v)
        A.basis z x τ hτ i j
    · exact IntertwiningBasis.CM.compact_projector_intertwines_second K D.ball D.places (FourSplittings.CM.newThetaSigns K v)
        A.basis z x τ hτ i j

theorem original_projector_parameter_value (z : HeckeCycles.GeometricSource.CM.BallChart) (w : ComplexTransition.CM.TotalAmbient K)
    (i : Fin 2) (τ : Fin D.places.count) :
    Symplectic.CM.galoisToPaired K D.places (TotalProjector.CM.totalSourceProjector K D.ball D.places (FourSplittings.CM.initialThetaSigns K v) z w i) τ =
      parameterProjectorValue K D.ball D.places (ApproximationSequence.CM.oldCompactPeriods K D) z w i τ := by
  by_cases hτ : τ = D.places.distinguished
  · subst τ
    simp only [parameterProjectorValue, ite_true]
    have h := IntertwiningBasis.CM.distinguished_projector_intertwines K D.ball D.places (FourSplittings.CM.initialThetaSigns K v)
      (Pi.basisFun K (Fin 2)) z w i
    simpa only [complex_standard_basis_change] using h
  · simp only [parameterProjectorValue, ite_eq_right hτ]
    apply Prod.ext <;> funext j
    · have h := IntertwiningBasis.CM.compact_projector_intertwines_first K D.ball D.places (FourSplittings.CM.initialThetaSigns K v)
        (Pi.basisFun K (Fin 2)) z w τ hτ i j
      simpa only [complex_standard_basis_change, ApproximationSequence.CM.oldCompactPeriods] using h
    · have h := IntertwiningBasis.CM.compact_projector_intertwines_second K D.ball D.places (FourSplittings.CM.initialThetaSigns K v)
        (Pi.basisFun K (Fin 2)) z w τ hτ i j
      simpa only [complex_standard_basis_change, ApproximationSequence.CM.oldCompactPeriods] using h

/-- The actual transported projectors converge on every vector, at every
ball point. The arithmetic input is the proved sequence of compact periods. -/
theorem approximation_projectors_tendsto (z : HeckeCycles.GeometricSource.CM.BallChart) (w : ComplexTransition.CM.TotalAmbient K) :
    Tendsto (fun n => TotalProjector.CM.approximationProjector K D (ApproximationSequence.CM.approximationSequence K D n) z w) atTop
      (𝓝 (TotalProjector.CM.totalSourceProjector K D.ball D.places (FourSplittings.CM.initialThetaSigns K v) z w)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have hp : Tendsto
      (fun n => Symplectic.CM.galoisToPaired K D.places
        (TotalProjector.CM.approximationProjector K D (ApproximationSequence.CM.approximationSequence K D n) z w i)) atTop
      (𝓝 (Symplectic.CM.galoisToPaired K D.places
        (TotalProjector.CM.totalSourceProjector K D.ball D.places (FourSplittings.CM.initialThetaSigns K v) z w i))) := by
    apply tendsto_pi_nhds.mpr
    intro τ
    simp only [approximation_projector_parameter_value, original_projector_parameter_value]
    exact ((parameter_projector_value_continuous K D.ball D.places z w i τ).tendsto _).comp
      (ApproximationSequence.CM.sequence_compact_periods_tendsto K D)
  have h := ((Symplectic.CM.galoisToPaired K D.places).symm.toContinuousLinearEquiv.continuous.tendsto _).comp hp
  change Tendsto (fun n => (Symplectic.CM.galoisToPaired K D.places).symm
    (Symplectic.CM.galoisToPaired K D.places (TotalProjector.CM.approximationProjector K D (ApproximationSequence.CM.approximationSequence K D n) z w i))) atTop
    (𝓝 ((Symplectic.CM.galoisToPaired K D.places).symm (Symplectic.CM.galoisToPaired K D.places
      (TotalProjector.CM.totalSourceProjector K D.ball D.places (FourSplittings.CM.initialThetaSigns K v) z w i)))) at h
  simpa only [LinearEquiv.symm_apply_apply] using h

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ProjectorParameters.CM
