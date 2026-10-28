import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceFrameComponents

/-! # Source Intrinsic Transition -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicTransition.CM

noncomputable section

section

/-! Exact index and coefficient equivalences between the two source
line blocks and the native tensor frame. -/

open scoped Classical _root_.NumberField
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]

def sourceTotalIndexEquiv (places : HeckeCycles.GeometricSource.CM.Places K) :
    PeriodTotal.CM.TotalPositions K places ≃ Fin places.count × (Fin 3 × Fin 2) where
  toFun p := Sum.elim (fun vi => (vi.1, vi.2, 0)) (fun vi => (vi.1, vi.2, 1)) p
  invFun p := SourceFrameComponents.CM.sourceTotalSlot K places p.1 p.2.1 p.2.2
  left_inv p := by cases p <;> rfl
  right_inv p := by rcases p with ⟨v, i, j⟩; fin_cases j <;> rfl

omit [IsGalois ℚ K] in
theorem source_total_index_pairing (places : HeckeCycles.GeometricSource.CM.Places K)
    (x y : ((Fin places.count × (Fin 3 × Fin 2)) ⊕ (Fin places.count × (Fin 3 × Fin 2))) → ℚ) :
    RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing
      (fun i => x (((sourceTotalIndexEquiv K places).sumCongr (sourceTotalIndexEquiv K places)) i))
      (fun i => y (((sourceTotalIndexEquiv K places).sumCongr (sourceTotalIndexEquiv K places)) i)) =
      RepresentationTheory.Theta.Adelic.DataTheta.standardPairing x y :=
  Equiv.sum_comp (sourceTotalIndexEquiv K places)
    (fun i => x (.inl i) * y (.inr i) - x (.inr i) * y (.inl i))

variable {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d)

theorem direct_source_frame_coefficients_bijective :
    Function.Bijective (SourceFrameComponents.CM.directSourceFrameCoefficients K Q) := by
  constructor
  · intro u w h
    funext p
    let i := sourceTotalIndexEquiv K places p
    have hi := congrFun h i
    change SourceFrameComponents.CM.directSourceFrameScale K Q i.1 i.2 * u ((sourceTotalIndexEquiv K places).symm i) =
      SourceFrameComponents.CM.directSourceFrameScale K Q i.1 i.2 * w ((sourceTotalIndexEquiv K places).symm i) at hi
    have hu := mul_left_cancel₀ (SourceFrameComponents.CM.direct_source_frame_scale_ne_zero K Q i.1 i.2) hi
    simpa only [i, Equiv.symm_apply_apply] using hu
  · intro w
    let e := sourceTotalIndexEquiv K places
    refine ⟨fun p => w (e p) / SourceFrameComponents.CM.directSourceFrameScale K Q (e p).1 (e p).2, ?_⟩
    funext i
    change SourceFrameComponents.CM.directSourceFrameScale K Q i.1 i.2 *
      (w (e (e.symm i)) / SourceFrameComponents.CM.directSourceFrameScale K Q (e (e.symm i)).1 (e (e.symm i)).2) = w i
    rw [e.apply_symm_apply]
    exact mul_div_cancel₀ _ (SourceFrameComponents.CM.direct_source_frame_scale_ne_zero K Q i.1 i.2)

def directSourceFrameCoefficientEquiv : (PeriodTotal.CM.TotalPositions K places → ℂ) ≃ₗ[ℂ]
    (Fin places.count × (Fin 3 × Fin 2) → ℂ) :=
  LinearEquiv.ofBijective (SourceFrameComponents.CM.directSourceFrameCoefficients K Q) (direct_source_frame_coefficients_bijective K Q)

end

section

/-! The fixed change from the original total rational coordinates to
the native tensor coordinates is an actual rational symplectic matrix. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true)
  (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)

def directSourceIndexedRationalCoordinates :
    TransportNew.CM.TensorPositions K ≃ₗ[ℚ] ((PeriodTotal.CM.TotalPositions K places ⊕ PeriodTotal.CM.TotalPositions K places) → ℚ) :=
  (IntrinsicCoordinates.CM.directSourceRationalCoordinates K Q.delta Q.delta_imaginary Q.delta_ne_zero
    B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B) Q.a
    (BallArithmetic.CM.direct_source_a_fixed K Q) (BallArithmetic.CM.direct_source_a_ne_zero K Q)
    (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother)).trans
      (LinearEquiv.funCongrLeft ℚ ℚ ((sourceTotalIndexEquiv K places).sumCongr (sourceTotalIndexEquiv K places)))

theorem direct_source_indexed_pairing (x y : TransportNew.CM.TensorPositions K) :
    RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (directSourceIndexedRationalCoordinates K Q hμ hother x)
      (directSourceIndexedRationalCoordinates K Q hμ hother y) =
      Algebra.trace ℚ K (Q.delta * TransportNew.CM.tensorHermitian K B.b Q.a x y) := by
  let r := IntrinsicCoordinates.CM.directSourceRationalCoordinates K Q.delta Q.delta_imaginary Q.delta_ne_zero
    B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B) Q.a
    (BallArithmetic.CM.direct_source_a_fixed K Q) (BallArithmetic.CM.direct_source_a_ne_zero K Q) (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother)
  change RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (fun i => r x (((sourceTotalIndexEquiv K places).sumCongr
    (sourceTotalIndexEquiv K places)) i)) (fun i => r y (((sourceTotalIndexEquiv K places).sumCongr
    (sourceTotalIndexEquiv K places)) i)) = _
  refine (source_total_index_pairing K places (r x) (r y)).trans ?_
  exact IntrinsicCoordinates.CM.direct_source_rational_coordinates_pairing K Q.delta Q.delta_imaginary Q.delta_ne_zero
    B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B) Q.a
    (BallArithmetic.CM.direct_source_a_fixed K Q) (BallArithmetic.CM.direct_source_a_ne_zero K Q)
    (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother) x y

variable (C : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)

def sourceNativeTransitionLinear :
    ((PeriodTotal.CM.TotalPositions K places ⊕ PeriodTotal.CM.TotalPositions K places) → ℚ) ≃ₗ[ℚ]
      ((PeriodTotal.CM.TotalPositions K places ⊕ PeriodTotal.CM.TotalPositions K places) → ℚ) :=
  (PeriodTotal.CM.totalSymplecticCoordinates K C).symm.trans (directSourceIndexedRationalCoordinates K Q hμ hother)

def sourceNativeTransitionMatrix :
    Matrix (PeriodTotal.CM.TotalPositions K places ⊕ PeriodTotal.CM.TotalPositions K places)
      (PeriodTotal.CM.TotalPositions K places ⊕ PeriodTotal.CM.TotalPositions K places) ℚ :=
  LinearMap.toMatrix' (sourceNativeTransitionLinear K Q hμ hother C).toLinearMap

theorem source_native_transition_matrix_apply (x : TransportNew.CM.TensorPositions K) :
    (sourceNativeTransitionMatrix K Q hμ hother C).mulVec (PeriodTotal.CM.totalSymplecticCoordinates K C x) =
      directSourceIndexedRationalCoordinates K Q hμ hother x := by
  rw [sourceNativeTransitionMatrix, LinearMap.toMatrix'_mulVec]
  change directSourceIndexedRationalCoordinates K Q hμ hother
    ((PeriodTotal.CM.totalSymplecticCoordinates K C).symm (PeriodTotal.CM.totalSymplecticCoordinates K C x)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem source_native_transition_symplectic
    (hC : ∀ j, (C j).a = Q.a j ∧ (C j).delta = Q.delta) :
    sourceNativeTransitionMatrix K Q hμ hother C ∈ Matrix.symplecticGroup (PeriodTotal.CM.TotalPositions K places) ℚ := by
  apply RepresentationTheory.Hecke.RadialDilation.PairingTransport.Realization.preserving_coordinatePairing_symplectic
  intro x y
  obtain ⟨u, rfl⟩ := (PeriodTotal.CM.totalSymplecticCoordinates K C).surjective x
  obtain ⟨v, rfl⟩ := (PeriodTotal.CM.totalSymplecticCoordinates K C).surjective y
  rw [source_native_transition_matrix_apply, source_native_transition_matrix_apply,
    direct_source_indexed_pairing, PeriodTotal.CM.total_symplectic_coordinates_pairing K C Q.delta Q.a hC]

def sourceNativeSymplecticTransition
    (hC : ∀ j, (C j).a = Q.a j ∧ (C j).delta = Q.delta) :
    Matrix.symplecticGroup (PeriodTotal.CM.TotalPositions K places) ℚ :=
  ⟨sourceNativeTransitionMatrix K Q hμ hother C, source_native_transition_symplectic K Q hμ hother C hC⟩

end

/-! The fixed rational symplectic transition complexifies to the
literal source-to-native tensor map, as checked on all rational vectors. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

def indexedSwappedPhaseMap {I J V : Type} [AddCommMonoid V] [Module ℂ V] [TopologicalSpace V]
    (e : I ≃ J) (N : ((J ⊕ J) → ℂ) ≃L[ℂ] V) : ((I ⊕ I) → ℂ) →ₗ[ℂ] V where
  toFun α := N (RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (fun i => α ((e.sumCongr e).symm i)))
  map_add' α β := by
    have h : RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (fun i => (α + β) ((e.sumCongr e).symm i)) =
        RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (fun i => α ((e.sumCongr e).symm i)) + RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (fun i => β ((e.sumCongr e).symm i)) := by
      funext i
      cases i <;> rfl
    exact (congrArg N h).trans (N.map_add _ _)
  map_smul' c α := by
    have h : RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (fun i => (c • α) ((e.sumCongr e).symm i)) =
        c • RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (fun i => α ((e.sumCongr e).symm i)) := by
      funext i
      cases i <;> rfl
    exact (congrArg N h).trans (N.map_smul c _)

theorem indexed_swapped_phase_map_apply {I J V : Type}
    [AddCommMonoid V] [Module ℂ V] [TopologicalSpace V]
    (e : I ≃ J) (N : ((J ⊕ J) → ℂ) ≃L[ℂ] V) (α : (I ⊕ I) → ℂ) :
    indexedSwappedPhaseMap e N α = N (RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (fun i => α ((e.sumCongr e).symm i))) := rfl

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true)
  (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)

abbrev directSourcePhaseRealization :
    ((PeriodTotal.CM.TotalPositions K places ⊕ PeriodTotal.CM.TotalPositions K places) → ℂ) →ₗ[ℂ]
      RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother) :=
  indexedSwappedPhaseMap (sourceTotalIndexEquiv K places)
    (SourceComponents.CM.directSourceComparison K Q hμ hother).complexPhase

theorem direct_source_phase_rational (x : TransportNew.CM.TensorPositions K) :
    directSourcePhaseRealization K Q hμ hother
      (fun i => (directSourceIndexedRationalCoordinates K Q hμ hother x i : ℂ)) =
      SourceComponents.CM.directSourceComplexComponents K Q hμ hother (ComplexTransition.CM.totalEmbedding K x) := by
  let e := (sourceTotalIndexEquiv K places).sumCongr (sourceTotalIndexEquiv K places)
  let r := IntrinsicCoordinates.CM.directSourceRationalCoordinates K Q.delta Q.delta_imaginary Q.delta_ne_zero
    B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B) Q.a
    (BallArithmetic.CM.direct_source_a_fixed K Q) (BallArithmetic.CM.direct_source_a_ne_zero K Q) (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother)
  have hinput : RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (fun i => (directSourceIndexedRationalCoordinates K Q hμ hother x (e.symm i) : ℂ)) =
      (fun i => ((SourceComponents.CM.directSourceComparison K Q hμ hother).rationalPhase
        ((SourceComponents.CM.directSourceFrames K Q).rational.coordinates
          (QuadraticTensor.CM.quadraticTensorPosition K Q.delta Q.delta_imaginary Q.delta_ne_zero x)) i : ℂ)) := by
    refine funext (fun i : (Fin places.count × (Fin 3 × Fin 2)) ⊕
      (Fin places.count × (Fin 3 × Fin 2)) => ?_)
    cases i with
    | inl i =>
        change ((r x (e (e.symm (.inr i))) : ℚ) : ℂ) = ((r x (.inr i) : ℚ) : ℂ)
        exact congrArg (fun j => ((r x j : ℚ) : ℂ)) (e.apply_symm_apply (.inr i))
    | inr i =>
        change ((r x (e (e.symm (.inl i))) : ℚ) : ℂ) = ((r x (.inl i) : ℚ) : ℂ)
        exact congrArg (fun j => ((r x j : ℚ) : ℂ)) (e.apply_symm_apply (.inl i))
  change (SourceComponents.CM.directSourceComparison K Q hμ hother).complexPhase
    (RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (fun i => (directSourceIndexedRationalCoordinates K Q hμ hother x (e.symm i) : ℂ))) = _
  refine (congrArg (SourceComponents.CM.directSourceComparison K Q hμ hother).complexPhase hinput).trans ?_
  exact SourceComponents.CM.direct_source_complex_phase_rational K Q hμ hother x

variable (C : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)

theorem source_native_transition_complex_rational (x : TransportNew.CM.TensorPositions K) :
    (sourceNativeTransitionMatrix K Q hμ hother C).map (algebraMap ℚ ℂ) *ᵥ
      (fun i => (PeriodTotal.CM.totalSymplecticCoordinates K C x i : ℂ)) =
      fun i => (directSourceIndexedRationalCoordinates K Q hμ hother x i : ℂ) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap ℚ ℂ) (sourceNativeTransitionMatrix K Q hμ hother C)
    (PeriodTotal.CM.totalSymplecticCoordinates K C x) i).symm.trans
    (congrArg (algebraMap ℚ ℂ) (congrFun (source_native_transition_matrix_apply K Q hμ hother C x) i))

theorem source_native_complex_transition (w : ComplexTransition.CM.TotalAmbient K) :
    directSourcePhaseRealization K Q hμ hother
      ((sourceNativeTransitionMatrix K Q hμ hother C).map (algebraMap ℚ ℂ) *ᵥ
        ComplexTransition.CM.totalComplexCoordinates K C w) = SourceComponents.CM.directSourceComplexComponents K Q hμ hother w := by
  let f := (directSourcePhaseRealization K Q hμ hother).comp
    ((Matrix.toLin' ((sourceNativeTransitionMatrix K Q hμ hother C).map (algebraMap ℚ ℂ))).comp
      (ComplexTransition.CM.totalComplexCoordinates K C).toLinearMap)
  have he : f = SourceComponents.CM.directSourceComplexComponents K Q hμ hother := by
    apply ComplexTransition.CM.linear_maps_eq_of_rational_coordinates (PeriodTotal.CM.totalSymplecticCoordinates K C)
      (ComplexTransition.CM.totalComplexCoordinates K C) (ComplexTransition.CM.totalEmbedding K) (ComplexTransition.CM.total_complex_coordinates_embedding K C)
    intro x
    change directSourcePhaseRealization K Q hμ hother
      ((sourceNativeTransitionMatrix K Q hμ hother C).map (algebraMap ℚ ℂ) *ᵥ
        ComplexTransition.CM.totalComplexCoordinates K C (ComplexTransition.CM.totalEmbedding K x)) = _
    rw [ComplexTransition.CM.total_complex_coordinates_embedding, source_native_transition_complex_rational,
      direct_source_phase_rational]
  exact LinearMap.congr_fun he w

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicTransition.CM
