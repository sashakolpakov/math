import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalSplitting
import OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic
import OAI.RepresentationTheory.Theta.Geometric.LinearTheta

/-! # Theta Transformation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaTransformation

noncomputable section

/-! The actual theta series transforms under the constructed rational
SU splitting, with the native half-determinant cocycle. -/

open OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.Construction
open OAI.RepresentationTheory.Theta.Geometric.LinearTheta
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

theorem native_theta_transformation (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3)) (x : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain})
    (w : Fin s × Fin 3 → ℂ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta (D.finite.action (RationalSplitting.nativeRationalFiniteSplitting E P hP hμ v hv e he D g) φ)
        (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he (g • x))
        ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E P e v he g)).jacobiChange
          (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he x) w) =
      HalfCocycle.nativeHalfFactor E P hP hμ v hv e he g x *
        (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E P e v he g))
          (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he x) w * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta φ (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he x) w) := by
  have h := RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.rational_theta_invariant D (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E P e v he g)
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor (RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he x) w) φ)
  have ht := Finite.Complement.Weil.finiteComplement_tensor D (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E P e v he)
    (RationalSplitting.nativeRationalRealSplitting E P hP hμ v hv e he D)
    (RationalSplitting.nativeRationalRealSplitting_covers E P hP hμ v hv e he D) g
    (RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianTest D (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he x) w) φ
  rw [ht, (RationalSplitting.nativeRationalRealSplitting_gaussian E P hP hμ v hv e he D g).2 x w,
    RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.Construction.thetaFunctional_tensor_smul, RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.thetaFunctional_gaussian_tensor,
    RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.thetaFunctional_gaussian_tensor, UnitaryPeriod.nativePeriod_unitary E P hP hμ v hv e he g x] at h
  have ha : HalfCocycle.nativeHalfFactor E P hP hμ v hv e he g x ≠ 0 := by
    intro hz
    have hs := HalfCocycle.nativeHalfFactor_sq E P hP hμ v hv e he g x
    rw [hz, zero_pow (by decide)] at hs
    exact RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.denominatorDet_ne_zero _ _ hs.symm
  apply mul_left_cancel₀ (mul_ne_zero (inv_ne_zero ha)
    (inv_ne_zero (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor_ne_zero (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E P e v he g))
      (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he x) w)))
  unfold RationalSplitting.nativeRationalFiniteSplitting
  rw [h]
  field_simp [ha, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor_ne_zero]

theorem native_first_theta_covariance (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin s × Fin 3)) (x : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst (D.finite.action (RationalSplitting.nativeRationalFiniteSplitting E P hP hμ v hv e he D g) φ)
        (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he (g • x))).comp
        ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E P e v he g)).jacobiChange
          (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he x)) =
      HalfCocycle.nativeHalfFactor E P hP hμ v hv e he g x • RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst φ (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he x) :=
  ComplexMultiplication.ThetaCovariance.CM.theta_first_derivative_covariance _
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E P e v he g)).thetaCorrectionForm
      (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he x)) _
    (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst_hasFDerivAt φ (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he x))
    (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst_hasFDerivAt _ (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he (g • x)))
    (native_theta_transformation E P hP hμ v hv e he D g φ x)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaTransformation
