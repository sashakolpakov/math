import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoordinateComparison
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComplexTransition
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallActionMatrix

/-! # Source Symplectic Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceSymplecticAction.CM

noncomputable section

/-! ThetaCycle: the rational ball transformation acts in the original
symplectic coordinates. Its scalar extension is the literal action at
every Galois embedding, with the original coordinates retained. -/

open scoped Classical _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K]
  [NumberField.IsCMField K] {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}

def sourceRationalAction (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) :
    (Sum (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) → ℚ) ≃ₗ[ℚ]
      (Sum (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) → ℚ) :=
  (CoordinateComparison.CM.sumCoordinates K C).symm.trans ((g.restrictScalars ℚ).trans (CoordinateComparison.CM.sumCoordinates K C))

def sourceRationalMatrix (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) :
    Matrix (Sum (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places))
      (Sum (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places)) ℚ :=
  LinearMap.toMatrix' (sourceRationalAction K C g).toLinearMap

theorem source_rational_matrix_apply (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (x : HeckeCycles.GeometricSource.CM.Vec K) :
    (sourceRationalMatrix K C g).mulVec (CoordinateComparison.CM.sumCoordinates K C x) =
      CoordinateComparison.CM.sumCoordinates K C (g x) := by
  rw [sourceRationalMatrix, LinearMap.toMatrix'_mulVec]
  exact congrArg (fun y => CoordinateComparison.CM.sumCoordinates K C (g y)) ((CoordinateComparison.CM.sumCoordinates K C).symm_apply_apply x)

theorem source_rational_matrix_symplectic (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
    (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y) :
    sourceRationalMatrix K C g ∈ Matrix.symplecticGroup (HeckeCycles.GeometricSource.CM.Positions K places) ℚ := by
  apply RepresentationTheory.Hecke.RadialDilation.PairingTransport.Realization.preserving_coordinatePairing_symplectic
  intro x y
  obtain ⟨u, rfl⟩ := (CoordinateComparison.CM.sumCoordinates K C).surjective x
  obtain ⟨v, rfl⟩ := (CoordinateComparison.CM.sumCoordinates K C).surjective y
  rw [source_rational_matrix_apply, source_rational_matrix_apply,
    CoordinateComparison.CM.sumCoordinates_pairing, CoordinateComparison.CM.sumCoordinates_pairing, RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization.rationalTraceForm_apply,
    RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization.rationalTraceForm_apply, NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.trace_matrix_diagonal,
    NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.trace_matrix_diagonal]
  exact congrArg (fun a => Algebra.trace ℚ K (C.delta * C.a * a)) (hg u v)

def sourceBallSymplectic (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
    (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y) :
    Matrix.symplecticGroup (HeckeCycles.GeometricSource.CM.Positions K places) ℚ :=
  ⟨sourceRationalMatrix K C g, source_rational_matrix_symplectic K C g hg⟩

variable [IsGalois ℚ K]

def ballEmbeddingMatrix (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (τ : Gal(K/ℚ)) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  (LinearMap.toMatrix' g.toLinearMap).map (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K τ)

def ballAmbientAction (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) : HeckeCycles.GeometricSource.CM.Ambient K →ₗ[ℂ] HeckeCycles.GeometricSource.CM.Ambient K :=
  LinearMap.pi (fun τ => (Matrix.toLin' (ballEmbeddingMatrix K g τ)).comp (LinearMap.proj τ))

omit [NumberField K] [NumberField.IsCMField K] in
theorem ball_ambient_action_embedding (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (x : HeckeCycles.GeometricSource.CM.Vec K) :
    ballAmbientAction K g (HeckeCycles.GeometricSource.CM.embeddingCoordinates K x) = HeckeCycles.GeometricSource.CM.embeddingCoordinates K (g x) := by
  funext τ i
  have he := congrArg (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K τ)
    (congrFun (LinearMap.toMatrix'_mulVec g.toLinearMap x) i)
  simpa only [ballAmbientAction, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Matrix.toLin'_apply, ballEmbeddingMatrix, Matrix.mulVec,
    dotProduct, map_sum, map_mul, Matrix.map_apply] using! he

def sourceComplexSumCoordinates (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places) :
    HeckeCycles.GeometricSource.CM.Ambient K ≃ₗ[ℂ] (Sum (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) → ℂ) :=
  C.complex.trans (LinearEquiv.sumArrowLequivProdArrow
    (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) ℂ ℂ).symm

omit [IsGalois ℚ K] in
theorem source_complex_sum_coordinates_embedding (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (x : HeckeCycles.GeometricSource.CM.Vec K) :
    sourceComplexSumCoordinates K C (HeckeCycles.GeometricSource.CM.embeddingCoordinates K x) =
      fun i => (CoordinateComparison.CM.sumCoordinates K C x i : ℂ) := by
  change (LinearEquiv.sumArrowLequivProdArrow _ _ ℂ ℂ).symm
    (C.complex (HeckeCycles.GeometricSource.CM.embeddingCoordinates K x)) = _
  rw [C.extends_rational]
  funext i
  cases i <;> rfl

theorem source_rational_matrix_complex_action (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
    (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (w : HeckeCycles.GeometricSource.CM.Ambient K) :
    (sourceRationalMatrix K C g).map (algebraMap ℚ ℂ) *ᵥ sourceComplexSumCoordinates K C w =
      sourceComplexSumCoordinates K C (ballAmbientAction K g w) := by
  let f := (Matrix.toLin' ((sourceRationalMatrix K C g).map (algebraMap ℚ ℂ))).comp
    (sourceComplexSumCoordinates K C).toLinearMap
  let h := (sourceComplexSumCoordinates K C).toLinearMap.comp (ballAmbientAction K g)
  have he : f = h := by
    apply ComplexTransition.CM.linear_maps_eq_of_rational_coordinates (CoordinateComparison.CM.sumCoordinates K C)
      (sourceComplexSumCoordinates K C) (HeckeCycles.GeometricSource.CM.embeddingCoordinates K)
      (source_complex_sum_coordinates_embedding K C)
    intro x
    change (sourceRationalMatrix K C g).map (algebraMap ℚ ℂ) *ᵥ
      sourceComplexSumCoordinates K C (HeckeCycles.GeometricSource.CM.embeddingCoordinates K x) =
        sourceComplexSumCoordinates K C (ballAmbientAction K g (HeckeCycles.GeometricSource.CM.embeddingCoordinates K x))
    rw [ball_ambient_action_embedding, source_complex_sum_coordinates_embedding,
      source_complex_sum_coordinates_embedding]
    have hx := congrArg (fun y => (algebraMap ℚ ℂ) ∘ y) (source_rational_matrix_apply K C g x)
    funext i
    exact (RingHom.map_mulVec (algebraMap ℚ ℂ) (sourceRationalMatrix K C g)
      (CoordinateComparison.CM.sumCoordinates K C x) i).symm.trans (congrFun hx i)
  exact LinearMap.congr_fun he w

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceSymplecticAction.CM
