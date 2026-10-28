import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaTransformation
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.MovingGradient
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyTheta

/-! # Frame Theta Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FrameThetaAction

noncomputable section

/-! The exact transformation of the native first-theta coordinates,
retaining the same rational finite splitting and every compact block. -/

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FamilyTheta.Multiplicity
open scoped Classical _root_.Matrix

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq PeriodAction.Multiplicity.nativeDomainAction

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
  (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
    Algebra.trace ℚ E (P.imaginaryScalar * Multiplicity.nativeTensorPairing E P v x y))
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)

theorem native_frameGradient_covariance (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3)) (x : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.frameGradient (Multiplicity.Period.nativeLowerFrame E P hP v e (g • x).val)
        (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst (D.finite.action (RationalSplitting.nativeRationalFiniteSplitting E P hP hμ v hv e he D g) φ)
          (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he (g • x))) =
      HalfCocycle.nativeHalfFactor E P hP hμ v hv e he g x •
        (GlobalFrame.nativeGlobalFrameMatrix E P v g x *ᵥ RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.frameGradient (Multiplicity.Period.nativeLowerFrame E P hP v e x)
          (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst φ (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he x))) :=
  MovingGradient.Frame.moving_frame_gradient _ _ _ _ _
    (PeriodFamily.Multiplicity.native_lowerFrame_det E P hP hμ v hv e he x x.property)
    (PeriodFamily.Multiplicity.native_lowerFrame_det E P hP hμ v hv e he (g • x).val (g • x).property)
    (UnitaryPeriod.native_unitary_period_columns E P hP hμ v hv e he g x).2 _ _ _
    (ThetaTransformation.native_first_theta_covariance E P hP hμ v hv e he D g φ x)

theorem native_frame_theta_transform (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3)) (x : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    FamilyTheta.Multiplicity.nativeFrameTheta E P hP hμ v hv e he
        (D.finite.action (RationalSplitting.nativeRationalFiniteSplitting E P hP hμ v hv e he D g) φ) (g • x) =
      HalfCocycle.nativeHalfFactor E P hP hμ v hv e he g x •
        (UnitaryFrameAction.weightedDualCoordinates (P.μ P.b)
          (ArchFrame.archConjugateUnitaryBlock E P P.distinguished g) x *ᵥ
            FamilyTheta.Multiplicity.nativeFrameTheta E P hP hμ v hv e he φ x) := by
  funext i
  have h := congrFun (native_frameGradient_covariance E P hP hμ v hv e he D g φ x)
    (P.distinguished, i.succ)
  simp only [Pi.smul_apply, smul_eq_mul, GlobalFrame.nativeGlobalFrameMatrix_mulVec,
    GlobalFrame.nativeFramePlaceMatrix] at h
  change _ = HalfCocycle.nativeHalfFactor E P hP hμ v hv e he g x *
    (ArchFrame.nativeActiveFrameMatrix E P g x *ᵥ (fun j => RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.frameGradient (Multiplicity.Period.nativeLowerFrame E P hP v e x)
      (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst φ (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he x)) (P.distinguished, j))) i.succ at h
  rw [ArchFrame.nativeActiveFrameMatrix, UnitaryFrameAction.activeFrameMatrix_mulVec] at h
  fin_cases i <;>
    simpa [FamilyTheta.Multiplicity.nativeFrameTheta, RepresentationTheory.Hecke.RadialDilation.GeometricTheta.Realization.projectedFrameTheta, RepresentationTheory.Theta.Geometric.LinearTheta.firstThetaLinear, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ] using h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.FrameThetaAction
