import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateCalibration
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.JointDepth
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdmissibleAwayLevel

/-! # Preprime Calibration -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PreprimeCalibration.Intrinsic

noncomputable section

section

/-! A retained normalized test, calibrated source level, and joint principal
depth. All fields are chosen before a finite prime or a local lift. -/

open scoped Classical _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateCalibration.Multiplicity OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdmissibleAwayLevel.Approximation OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.JointDepth.TestTransport

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)

structure RetainedPreprimeData where
  coordinates : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ)
  pairing : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (coordinates x) (coordinates y) =
    Algebra.trace ℚ E (P.imaginaryScalar * Intrinsic.Multiplicity.nativeTensorPairing E P v x y)
  thetaTest : Intrinsic.NonzeroTest.NativeThetaTest E P hP hμ v hv coordinates pairing
  calibration : RationalTest.Intrinsic.RationalTestCalibration E P hP hμ v hv coordinates pairing W thetaTest.test
  depth : ℕ
  depth_pos : 0 < depth
  projective_dvd : PEL.ChosenProjectiveDepth.TestTransport.pelProjectiveDepth E P coordinates W thetaTest.test
    (AdmissibleAwayLevel.Approximation.admissible_lattice_fg E P hP) (AdmissibleAwayLevel.Approximation.admissible_lattice_span E P hP)
    (Intrinsic.NonzeroTest.nativeThetaTest_ne_zero E P hP hμ v hv coordinates pairing thetaTest)
    thetaTest.support thetaTest.level thetaTest.level_pos thetaTest.period ∣ depth
  source_depth : ∀ N : ℕ, depth ∣ N → ∀ g : CM.FiniteAway.Approximation.CMFiniteSU E P hP,
    CM.AwayPELLevel.Approximation.cmOriginalPELHomeomorph E P hP g ∈ P.adelicPrincipalLevel N → g ∈ calibration.sourceLevel

end

/-! Build the joint pre-prime data from an actually calibrated source level. -/

open scoped Classical _root_.Matrix

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoordinateCalibration.Multiplicity OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdmissibleAwayLevel.Approximation OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.JointDepth.TestTransport

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)

def retainedPreprimeOfCalibration
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
    (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
      Algebra.trace ℚ E (P.imaginaryScalar * Intrinsic.Multiplicity.nativeTensorPairing E P v x y))
    (T : Intrinsic.NonzeroTest.NativeThetaTest E P hP hμ v hv e he)
    (R : RationalTest.Intrinsic.RationalTestCalibration E P hP hμ v hv e he W T.test) :
    RetainedPreprimeData E P hP hμ v hv W := by
  let h := JointDepth.TestTransport.exists_retained_joint_depth E P hP e W T.test
    (AdmissibleAwayLevel.Approximation.admissible_lattice_fg E P hP) (AdmissibleAwayLevel.Approximation.admissible_lattice_span E P hP)
    (Intrinsic.NonzeroTest.nativeThetaTest_ne_zero E P hP hμ v hv e he T)
    T.support T.level T.level_pos T.period R.sourceLevel
  exact {
    coordinates := e
    pairing := he
    thetaTest := T
    calibration := R
    depth := h.choose
    depth_pos := h.choose_spec.1
    projective_dvd := h.choose_spec.2.1
    source_depth := h.choose_spec.2.2 }

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PreprimeCalibration.Intrinsic
