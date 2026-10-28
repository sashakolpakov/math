import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.HalfCocycle
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GaussianSplitting

/-! # Rational Splitting -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalSplitting

noncomputable section

/-! Construct real and finite rational SU splittings in PoissonAutomorphy's actual
two-fold cover from the same signed native period and frame. -/

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GaussianSplitting.Weil
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

def nativeRationalRealSplitting : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b →* MpR := by
  let : ConnectedSpace {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain} :=
    isConnected_iff_connectedSpace.mp (PeriodDomain.Multiplicity.native_domain_connected E P hP)
  exact GaussianSplitting.Weil.familyRealSplitting D (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E P e v he)
    (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he) (HalfCocycle.nativeHalfFactor E P hP hμ v hv e he)
    (PeriodDomain.Multiplicity.nativePeriod_continuous E P hP hμ v hv e he)
    (HalfCocycle.nativeHalfFactor_continuous E P hP hμ v hv e he)
    (HalfCocycle.nativeHalfFactor_sq E P hP hμ v hv e he)
    (UnitaryPeriod.nativePeriod_unitary E P hP hμ v hv e he)
    (HalfCocycle.nativeHalfFactor_one E P hP hμ v hv e he)
    (HalfCocycle.nativeHalfFactor_mul E P hP hμ v hv e he)

theorem nativeRationalRealSplitting_covers (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) :
    D.real.project (nativeRationalRealSplitting E P hP hμ v hv e he D g) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ ℝ) (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E P e v he g) := by
  let : ConnectedSpace {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain} :=
    isConnected_iff_connectedSpace.mp (PeriodDomain.Multiplicity.native_domain_connected E P hP)
  exact GaussianSplitting.Weil.familyRealSplitting_covers D (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E P e v he)
    (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he) (HalfCocycle.nativeHalfFactor E P hP hμ v hv e he)
    (PeriodDomain.Multiplicity.nativePeriod_continuous E P hP hμ v hv e he)
    (HalfCocycle.nativeHalfFactor_continuous E P hP hμ v hv e he)
    (HalfCocycle.nativeHalfFactor_sq E P hP hμ v hv e he)
    (UnitaryPeriod.nativePeriod_unitary E P hP hμ v hv e he)
    (HalfCocycle.nativeHalfFactor_one E P hP hμ v hv e he)
    (HalfCocycle.nativeHalfFactor_mul E P hP hμ v hv e he) g

def nativeRationalFiniteSplitting : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b →* MpF :=
  Finite.Complement.Weil.finiteComplement D (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E P e v he)
    (nativeRationalRealSplitting E P hP hμ v hv e he D)
    (nativeRationalRealSplitting_covers E P hP hμ v hv e he D)

theorem nativeRationalFiniteSplitting_covers (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) :
    D.finite.project (nativeRationalFiniteSplitting E P hP hμ v hv e he D g) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E P e v he g) :=
  Finite.Complement.Weil.finiteComplement_covers D _ _ _ g

theorem nativeRationalSplitting_factorization (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) :
    D.includeReal (nativeRationalRealSplitting E P hP hμ v hv e he D g) *
      D.includeFinite (nativeRationalFiniteSplitting E P hP hμ v hv e he D g) =
        D.rationalSplit (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E P e v he g) :=
  Finite.Complement.Weil.finiteComplement_factorization D _ _ _ g

theorem nativeRationalRealSplitting_gaussian (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) :
    GaussianLift.Weil.HasGaussianFamilyAction D (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he)
      (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E P e v he g) (HalfCocycle.nativeHalfFactor E P hP hμ v hv e he g)
      (nativeRationalRealSplitting E P hP hμ v hv e he D g) := by
  let : ConnectedSpace {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain} :=
    isConnected_iff_connectedSpace.mp (PeriodDomain.Multiplicity.native_domain_connected E P hP)
  exact GaussianLift.Weil.gaussianFamilyLift_spec D (PeriodFamily.Multiplicity.nativePeriod E P hP hμ v hv e he)
    (RationalPhaseColumn.Intrinsic.nativeRationalSymplectic E P e v he g) (HalfCocycle.nativeHalfFactor E P hP hμ v hv e he g)
    (PeriodDomain.Multiplicity.nativePeriod_continuous E P hP hμ v hv e he)
    (HalfCocycle.nativeHalfFactor_continuous E P hP hμ v hv e he g)
    (HalfCocycle.nativeHalfFactor_sq E P hP hμ v hv e he g)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.RationalSplitting
