import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationIntrinsicArithmetic
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MultiplicityArithmeticTransport
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntertwiningBasis

/-! # Concrete Approximation Complex Components -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationComplexComponents.CM

noncomputable section

section

/-! The actual complex multiplicity basis change agrees with the native
quadratic-algebra change at every original CM place, in both components.
Consequently the fixed-space tensor components recover the split frame. -/

open scoped Classical _root_.NumberField _root_.Matrix Kronecker
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

theorem identity_kronecker_mulVec {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ)
    (x : Fin 3 × Fin m → ℂ) (i : Fin 3) (j : Fin m) :
    ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ M).mulVec x (i, j) =
      M.mulVec (fun k => x (i, k)) j := by
  simp [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply]

theorem identity_kronecker_star_mulVec {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ)
    (x : Fin 3 × Fin m → ℂ) (i : Fin 3) (j : Fin m) :
    (((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ M).map star).mulVec x (i, j) =
      (M.map star).mulVec (fun k => x (i, k)) j := by
  simp [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply, apply_ite]

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
  (hid : ∀ i, (v i).val 1 = true)

def approximationComplexComponents : ComplexTransition.CM.TotalAmbient K →ₗ[ℂ]
    RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) :=
  (IntrinsicTensorComplexCoordinates.CM.nativePairedTensorComponents (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid)).comp
    (SourceComponents.CM.sourcePairedTensorCoordinates K D.places)

def approximationCoefficientComplexComponents : ComplexTransition.CM.TotalAmbient K →ₗ[ℂ]
    RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase (ConcreteApproximationIntrinsicArithmetic.CM.approximationCoefficientArithmetic K D A hid) :=
  (IntrinsicTensorComplexCoordinates.CM.nativePairedTensorComponents (ConcreteApproximationIntrinsicArithmetic.CM.approximationCoefficientArithmetic K D A hid)).comp
    (SourceComponents.CM.sourcePairedTensorCoordinates K D.places)

theorem approximation_native_multiplicity_matrix (τ : Fin D.places.count) :
    (MultiplicityArithmeticTransport.CM.nativeComplexMultiplicityBasis (ConcreteApproximationIntrinsicArithmetic.CM.approximationCoefficientArithmetic K D A hid)
      (QuadraticMultiplicityBasis.CM.quadraticMultiplicityBasis K D.pair.delta D.pair.delta_imaginary D.pair.delta_ne_zero A.basis) τ).val =
      Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix (HeckeCycles.ReferenceDatum.CM.embeddings K D.places τ) A.basis := by
  apply Matrix.ext
  intro i j
  change CMArchimedeanCoordinates.CM.sourceComplexCoordinate K D.places D.pair.delta D.pair.delta_imaginary D.pair.delta_ne_zero τ
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K D.pair.delta D.pair.delta_imaginary)
      (.inl (RealPlaces.CM.sourceRealPlaces K D.places τ))
      ((QuadraticMultiplicityBasis.CM.quadraticMultiplicityBasis K D.pair.delta D.pair.delta_imaginary D.pair.delta_ne_zero A.basis).val i j)) = _
  refine (congrArg (fun x => CMArchimedeanCoordinates.CM.sourceComplexCoordinate K D.places D.pair.delta D.pair.delta_imaginary
    D.pair.delta_ne_zero τ (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (maximalRealSubfield K)
      (QuadraticModel.CM.cmQuadraticParameter K D.pair.delta D.pair.delta_imaginary) (.inl (RealPlaces.CM.sourceRealPlaces K D.places τ)) x))
    (QuadraticMultiplicityBasis.CM.quadratic_multiplicity_basis_entry K D.pair.delta D.pair.delta_imaginary D.pair.delta_ne_zero A.basis i j)).trans ?_
  exact (CMArchimedeanCoordinates.CM.source_complex_coordinate_rational K D.places D.pair.delta D.pair.delta_imaginary D.pair.delta_ne_zero τ _).trans
    (congrArg (HeckeCycles.ReferenceDatum.CM.embeddings K D.places τ)
      ((QuadraticModel.CM.cmQuadraticEquiv K D.pair.delta D.pair.delta_imaginary D.pair.delta_ne_zero).apply_symm_apply _))

theorem approximation_source_paired_basis_change (w : ComplexTransition.CM.TotalAmbient K) :
    SourceComponents.CM.sourcePairedTensorCoordinates K D.places (ComplexTransition.CM.complexTensorBasisChange K A.basis w) =
      MultiplicityArithmeticTransport.CM.nativeMultiplicityPhaseAction (ConcreteApproximationIntrinsicArithmetic.CM.approximationCoefficientArithmetic K D A hid)
        (QuadraticMultiplicityBasis.CM.quadraticMultiplicityBasis K D.pair.delta D.pair.delta_imaginary D.pair.delta_ne_zero A.basis)
        (SourceComponents.CM.sourcePairedTensorCoordinates K D.places w) := by
  refine funext (fun τ : Fin D.places.count => ?_)
  apply Prod.ext
  · funext ij
    have hm := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ =>
      ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ M).mulVec
        (SourceComponents.CM.sourcePairedTensorCoordinates K D.places w τ).1 ij)
      (approximation_native_multiplicity_matrix K D A hid τ)
    have he := identity_kronecker_mulVec
      (Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix (HeckeCycles.ReferenceDatum.CM.embeddings K D.places τ) A.basis)
      (SourceComponents.CM.sourcePairedTensorCoordinates K D.places w τ).1 ij.1 ij.2
    exact (IntertwiningBasis.CM.paired_basis_change_first K D.places A.basis w ij.2 τ ij.1).trans (hm.trans he).symm
  · funext ij
    have hm := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ =>
      (((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ M).map star).mulVec
        (SourceComponents.CM.sourcePairedTensorCoordinates K D.places w τ).2 ij)
      (approximation_native_multiplicity_matrix K D A hid τ)
    have he := identity_kronecker_star_mulVec
      (Analysis.DifferentialForms.Coordinates.LocalApproximation.localBasisMatrix (HeckeCycles.ReferenceDatum.CM.embeddings K D.places τ) A.basis)
      (SourceComponents.CM.sourcePairedTensorCoordinates K D.places w τ).2 ij.1 ij.2
    exact (IntertwiningBasis.CM.paired_basis_change_second K D.places A.basis w ij.2 τ ij.1).trans (hm.trans he).symm

theorem approximation_complex_basis_components (w : ComplexTransition.CM.TotalAmbient K) :
    approximationComplexComponents K D A hid (ComplexTransition.CM.complexTensorBasisChange K A.basis w) =
      approximationCoefficientComplexComponents K D A hid w := by
  refine (congrArg (IntrinsicTensorComplexCoordinates.CM.nativePairedTensorComponents (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid))
    (approximation_source_paired_basis_change K D A hid w)).trans ?_
  exact MultiplicityArithmeticTransport.CM.transport_multiplicity_paired_components (ConcreteApproximationIntrinsicArithmetic.CM.approximationCoefficientArithmetic K D A hid)
    (QuadraticMultiplicityBasis.CM.quadraticMultiplicityBasis K D.pair.delta D.pair.delta_imaginary D.pair.delta_ne_zero A.basis)
    (QuadraticMultiplicityBasis.CM.quadratic_multiplicity_basis_congruence K D.pair.delta D.pair.delta_imaginary D.pair.delta_ne_zero
      D.pair.a (BallArithmetic.CM.direct_source_a_fixed K D.pair) (BallArithmetic.CM.direct_source_a_ne_zero K D.pair) A.basis A.orthogonal
      (ConcreteApproximationIntrinsicArithmetic.CM.approximation_native_coefficients_fixed K D A) (ConcreteApproximationIntrinsicArithmetic.CM.approximation_native_coefficients_nonzero K D A))
    (SourceComponents.CM.sourcePairedTensorCoordinates K D.places w)

end

/-! Every actual approximation uses the same fixed rational symplectic
transition from the original total source coordinates. Only its geometric
complex realization and period change. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
  (hid : ∀ i, (v i).val 1 = true)

def approximationPhaseRealization :
    ((PeriodTotal.CM.TotalPositions K D.places ⊕ PeriodTotal.CM.TotalPositions K D.places) → ℂ) →ₗ[ℂ]
      RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) :=
  SourceIntrinsicTransition.CM.indexedSwappedPhaseMap (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places) (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid).complexPhase

theorem approximation_rational_tensor_components (x : TransportNew.CM.TensorPositions K) :
    RepresentationTheory.Theta.Adelic.BallGeometryData.realTensorComponents (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid)
      (fun τ j => RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (maximalRealSubfield K)
        (QuadraticModel.CM.cmQuadraticParameter K D.pair.delta D.pair.delta_imaginary) (.inl (RealPlaces.CM.sourceRealPlaces K D.places τ))
        (QuadraticTensor.CM.quadraticTensorPosition K D.pair.delta D.pair.delta_imaginary D.pair.delta_ne_zero x j)) =
      approximationComplexComponents K D A hid (ComplexTransition.CM.totalEmbedding K x) := by
  change _ = IntrinsicTensorComplexCoordinates.CM.nativePairedTensorComponents (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid)
    (SourceComponents.CM.sourcePairedTensorCoordinates K D.places (ComplexTransition.CM.totalEmbedding K x))
  rw [SourceComponents.CM.source_paired_tensor_embedding]
  apply IntrinsicTensorComplexCoordinates.CM.native_real_tensor_components_of_values
  intro τ j
  exact (CMArchimedeanCoordinates.CM.source_complex_coordinate_rational K D.places D.pair.delta D.pair.delta_imaginary D.pair.delta_ne_zero τ
    (QuadraticTensor.CM.quadraticTensorPosition K D.pair.delta D.pair.delta_imaginary D.pair.delta_ne_zero x j)).trans
    (congrArg (HeckeCycles.ReferenceDatum.CM.embeddings K D.places τ)
      ((QuadraticModel.CM.cmQuadraticEquiv K D.pair.delta D.pair.delta_imaginary D.pair.delta_ne_zero).apply_symm_apply _))

theorem approximation_phase_rational (x : TransportNew.CM.TensorPositions K) :
    approximationPhaseRealization K D A hid
      (fun i => (SourceIntrinsicTransition.CM.directSourceIndexedRationalCoordinates K D.pair (ConcreteApproximationIntrinsicArithmetic.CM.initial_native_active_signs K D hid)
        D.ball.other_place x i : ℂ)) =
      approximationComplexComponents K D A hid (ComplexTransition.CM.totalEmbedding K x) := by
  let P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames (maximalRealSubfield K)
      (QuadraticModel.CM.cmQuadraticParameter K D.pair.delta (ConcreteApproximationIntrinsicArithmetic.CM.setup_delta_imaginary K D)) 3 2
      (CMGlobalFrames.CM.cmHermitianUnit K D.pair.delta (ConcreteApproximationIntrinsicArithmetic.CM.setup_delta_imaginary K D) D.ball.b (ConcreteApproximationIntrinsicArithmetic.CM.setup_ball_fixed K D)
        (ConcreteApproximationIntrinsicArithmetic.CM.setup_ball_nonzero K D))
      (BallArithmetic.CM.directSourceSkewUnit K D.pair.delta (ConcreteApproximationIntrinsicArithmetic.CM.setup_delta_imaginary K D) (ConcreteApproximationIntrinsicArithmetic.CM.setup_delta_ne_zero K D) D.pair.a
        (ConcreteApproximationIntrinsicArithmetic.CM.setup_a_fixed K D) (ConcreteApproximationIntrinsicArithmetic.CM.setup_a_nonzero K D)) := SourceComponents.CM.directSourceFrames K D.pair
  let e := (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places).sumCongr (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places)
  let r := IntrinsicCoordinates.CM.directSourceRationalCoordinates K D.pair.delta D.pair.delta_imaginary D.pair.delta_ne_zero
    D.ball.b D.ball.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K D.ball) D.pair.a
    (BallArithmetic.CM.direct_source_a_fixed K D.pair) (BallArithmetic.CM.direct_source_a_ne_zero K D.pair)
    (BallArithmetic.CM.directSourceBallArithmeticData K D.pair (ConcreteApproximationIntrinsicArithmetic.CM.initial_native_active_signs K D hid) D.ball.other_place)
  have hp : RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (fun i => (SourceIntrinsicTransition.CM.directSourceIndexedRationalCoordinates K D.pair
      (ConcreteApproximationIntrinsicArithmetic.CM.initial_native_active_signs K D hid) D.ball.other_place x (e.symm i) : ℂ)) =
      (fun i => ((ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid).rationalPhase
        (P.rational.coordinates
          (QuadraticTensor.CM.quadraticTensorPosition K D.pair.delta D.pair.delta_imaginary D.pair.delta_ne_zero x)) i : ℂ)) := by
    refine funext (fun i : (Fin D.places.count × (Fin 3 × Fin 2)) ⊕
      (Fin D.places.count × (Fin 3 × Fin 2)) => ?_)
    cases i with
    | inl i =>
        change ((r x (e (e.symm (.inr i))) : ℚ) : ℂ) = ((r x (.inr i) : ℚ) : ℂ)
        exact congrArg (fun j => ((r x j : ℚ) : ℂ)) (e.apply_symm_apply (.inr i))
    | inr i =>
        change ((r x (e (e.symm (.inl i))) : ℚ) : ℂ) = ((r x (.inl i) : ℚ) : ℂ)
        exact congrArg (fun j => ((r x j : ℚ) : ℂ)) (e.apply_symm_apply (.inl i))
  have hn := @IntrinsicTensorComplexCoordinates.CM.native_complex_phase_rational_tensor (maximalRealSubfield K) _ (BallArithmetic.CM.directNativeRealNumberField K)
    (QuadraticModel.CM.cmQuadraticParameter K D.pair.delta (ConcreteApproximationIntrinsicArithmetic.CM.setup_delta_imaginary K D)) 2
    (CMGlobalFrames.CM.cmHermitianUnit K D.pair.delta (ConcreteApproximationIntrinsicArithmetic.CM.setup_delta_imaginary K D) D.ball.b (ConcreteApproximationIntrinsicArithmetic.CM.setup_ball_fixed K D)
      (ConcreteApproximationIntrinsicArithmetic.CM.setup_ball_nonzero K D))
    (BallArithmetic.CM.directSourceSkewUnit K D.pair.delta (ConcreteApproximationIntrinsicArithmetic.CM.setup_delta_imaginary K D) (ConcreteApproximationIntrinsicArithmetic.CM.setup_delta_ne_zero K D) D.pair.a
      (ConcreteApproximationIntrinsicArithmetic.CM.setup_a_fixed K D) (ConcreteApproximationIntrinsicArithmetic.CM.setup_a_nonzero K D))
    (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid)
    P
    (QuadraticTensor.CM.quadraticTensorPosition K D.pair.delta D.pair.delta_imaginary D.pair.delta_ne_zero x)
  have he := hn.trans (approximation_rational_tensor_components K D A hid x)
  change (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid).complexPhase
    (RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (fun i => (SourceIntrinsicTransition.CM.directSourceIndexedRationalCoordinates K D.pair
      (ConcreteApproximationIntrinsicArithmetic.CM.initial_native_active_signs K D hid) D.ball.other_place x (e.symm i) : ℂ))) = _
  have hf := congrArg (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid).complexPhase hp
  dsimp only [ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison, P] at hf he
  exact hf.trans he

theorem approximation_original_complex_transition (w : ComplexTransition.CM.TotalAmbient K) :
    approximationPhaseRealization K D A hid
      ((SourceIntrinsicTransition.CM.sourceNativeTransitionMatrix K D.pair (ConcreteApproximationIntrinsicArithmetic.CM.initial_native_active_signs K D hid) D.ball.other_place
        (fun j => (D.initialPeriods j).coordinates)).map (algebraMap ℚ ℂ) *ᵥ
        ComplexTransition.CM.totalComplexCoordinates K (fun j => (D.initialPeriods j).coordinates) w) =
      approximationComplexComponents K D A hid w := by
  let C := fun j => (D.initialPeriods j).coordinates
  let M := SourceIntrinsicTransition.CM.sourceNativeTransitionMatrix K D.pair (ConcreteApproximationIntrinsicArithmetic.CM.initial_native_active_signs K D hid) D.ball.other_place C
  let f := (approximationPhaseRealization K D A hid).comp
    ((Matrix.toLin' (M.map (algebraMap ℚ ℂ))).comp (ComplexTransition.CM.totalComplexCoordinates K C).toLinearMap)
  have he : f = approximationComplexComponents K D A hid := by
    apply ComplexTransition.CM.linear_maps_eq_of_rational_coordinates (PeriodTotal.CM.totalSymplecticCoordinates K C)
      (ComplexTransition.CM.totalComplexCoordinates K C) (ComplexTransition.CM.totalEmbedding K) (ComplexTransition.CM.total_complex_coordinates_embedding K C)
    intro x
    change approximationPhaseRealization K D A hid
      (M.map (algebraMap ℚ ℂ) *ᵥ ComplexTransition.CM.totalComplexCoordinates K C (ComplexTransition.CM.totalEmbedding K x)) = _
    have hc := congrArg (fun y => approximationPhaseRealization K D A hid (M.map (algebraMap ℚ ℂ) *ᵥ y))
      (ComplexTransition.CM.total_complex_coordinates_embedding K C x)
    have hr := congrArg (approximationPhaseRealization K D A hid)
      (SourceIntrinsicTransition.CM.source_native_transition_complex_rational K D.pair (ConcreteApproximationIntrinsicArithmetic.CM.initial_native_active_signs K D hid)
        D.ball.other_place C x)
    exact hc.trans (hr.trans (approximation_phase_rational K D A hid x))
  exact LinearMap.congr_fun he w

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationComplexComponents.CM
