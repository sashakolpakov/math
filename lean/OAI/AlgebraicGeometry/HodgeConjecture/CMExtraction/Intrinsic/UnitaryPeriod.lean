import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.GlobalFrame
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodAction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.MovingFrame

/-! # Unitary Period -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.UnitaryPeriod

noncomputable section

/-! Equivariance of the actual signed native Siegel period and its
determinant denominator under the rational special-unitary group. -/

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodAction.Multiplicity
open scoped Classical _root_.Matrix

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq PeriodAction.Multiplicity.nativeDomainAction

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (P.imaginaryScalar * Multiplicity.nativeTensorPairing E P v x y))

theorem native_unitary_frame_block_equations
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    let S := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E P e v he g)).complexify
    let T := GlobalFrame.nativeGlobalFrameMatrix E P v g z
    S.A * Multiplicity.Period.nativeUpperFrame E P hP v e z + S.B * Multiplicity.Period.nativeLowerFrame E P hP v e z =
        Multiplicity.Period.nativeUpperFrame E P hP v e (g • z).val * T ∧
    S.C * Multiplicity.Period.nativeUpperFrame E P hP v e z + S.D * Multiplicity.Period.nativeLowerFrame E P hP v e z =
        Multiplicity.Period.nativeLowerFrame E P hP v e (g • z).val * T := by
  apply MovingFrame.moving_frame_block_equations
    (RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization.rationalCoordinates E P.embeddings hP.1 e) (Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Multiplicity.nativeMatrix E P))
    P.distinguished (Multiplicity.Period.nativeCompactSigns E P v) z (g • z).val (ArchUnitaryCoordinates.Intrinsic.pairedUnitaryEnd E P g)
  · exact GlobalFrame.native_global_frame_transform E P v hP g z z.property
  · intro u
    rw [ArchUnitaryCoordinates.Intrinsic.rational_matrix_realizes_unitary E P hP.1 e]
    congr 1
    ext i j
    cases i <;> cases j <;>
      simp [RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.blocks, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp, ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.complexify, RationalPhaseColumn.Intrinsic.nativeRationalSymplectic,
        Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

theorem native_unitary_period_columns
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    let S := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E P e v he g)).complexify
    let Z := PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he z
    let Z' := PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he (g • z)
    let Q := Multiplicity.Period.nativeLowerFrame E P hP v e z
    let Q' := Multiplicity.Period.nativeLowerFrame E P hP v e (g • z).val
    let T := GlobalFrame.nativeGlobalFrameMatrix E P v g z
    (S.A * Z.matrix + S.B) * Q = Z'.matrix * Q' * T ∧
      S.denominator Z.matrix * Q = Q' * T := by
  have h := native_unitary_frame_block_equations E P hP v e he g z
  dsimp only at h ⊢
  constructor
  · rw [Matrix.add_mul, Matrix.mul_assoc, PeriodFamily.Multiplicity.nativePeriod_columns, PeriodFamily.Multiplicity.nativePeriod_columns]
    exact h.1
  · rw [ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.denominator, Matrix.add_mul, Matrix.mul_assoc, PeriodFamily.Multiplicity.nativePeriod_columns]
    exact h.2

theorem nativePeriod_unitary
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E P e v he g)).transformSiegel
        (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he z) = PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he (g • z) :=
  MovingFrame.moving_frame_period _ _ _ _ _ _ (PeriodFamily.Multiplicity.native_lowerFrame_det E P hP hμ v hv e he z z.property)
    (native_unitary_period_columns E P hP hμ v hv e he g z).1
    (native_unitary_period_columns E P hP hμ v hv e he g z).2

theorem nativePeriod_unitary_denominator
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.denominatorDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E P e v he g))
        (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.ofSiegel (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he z)) =
      (Multiplicity.Period.nativeLowerFrame E P hP v e (g • z).val).det *
        RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator (ArchFrame.archUnitaryBlock E P P.distinguished g) z ^ 2 /
          (Multiplicity.Period.nativeLowerFrame E P hP v e z).det := by
  have h := MovingFrame.moving_frame_determinant _ _ _ _ _
    (PeriodFamily.Multiplicity.native_lowerFrame_det E P hP hμ v hv e he z z.property)
    (native_unitary_period_columns E P hP hμ v hv e he g z).2
  rw [GlobalFrame.nativeGlobalFrameMatrix_det E P v hP g z] at h
  exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.UnitaryPeriod
