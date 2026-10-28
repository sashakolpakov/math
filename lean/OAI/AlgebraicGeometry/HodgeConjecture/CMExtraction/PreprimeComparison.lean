import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PreprimeCalibration
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SourceTestOpenLevel

/-! # Preprime Comparison -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.CMExtraction.PreprimeComparison.Multiplicity

/-! Construct the retained prime-independent data from one complete AdelicTheta comparison. -/

open scoped Classical _root_.Matrix _root_.NumberField
open _root_.Matrix _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates
open OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicCovariance OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection

attribute [local instance] Intrinsic.PeriodAction.Multiplicity.nativeDomainAction Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (hs : 2 ≤ s) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP)
    (Intrinsic.OneTheta.Multiplicity.nativeOneSkew E P hP v) (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv))
  (hCoord : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification B (Intrinsic.OneTheta.Multiplicity.nativeOneFrames E P hP v))
  (hGeometry : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification B)
  (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneParameter E P hP) 3 1)
  (S : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneParameter E P hP) 3 1
    (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP) (Intrinsic.OneTheta.Multiplicity.nativeOneSkew E P hP v) (Intrinsic.OneTheta.Multiplicity.nativeOneParameterNonzero E P hP)
    C (Intrinsic.OneTheta.Multiplicity.nativeOneFrames E P hP v))

variable {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)

def retainedPreprimeOfComparison
    (hCovariance : RepresentationTheory.Theta.Adelic.DataTheta.Descent.RationalHeckeCovariance B (Intrinsic.OneTheta.Multiplicity.nativeOneFrames E P hP v)
      (Intrinsic.OneTheta.Multiplicity.nativeOneParameterNonzero E P hP) C S)
    (hDescent : RepresentationTheory.Theta.Adelic.DataTheta.Descent.CongruenceDescent B (Intrinsic.OneTheta.Multiplicity.nativeOneFrames E P hP v)
      (Intrinsic.OneTheta.Multiplicity.nativeOneParameterNonzero E P hP) C S) :
    PreprimeCalibration.Intrinsic.RetainedPreprimeData E P hP hμ v hv W := by
  let e := Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B
  let he := Intrinsic.OneCoordinates.Multiplicity.nativeOneRationalCoordinates_pairing E P hP hμ hs v hv B hCoord
  let T := Intrinsic.NonzeroTest.nativeThetaTest E P hP hμ v hv e he
  let hL := Intrinsic.SourceTestOpenLevel.Multiplicity.exists_native_source_test_level E P hP hμ hs v hv B C S hDescent
    (Intrinsic.TransportedForm.Multiplicity.nativeOneFiniteTest E P hP hμ hs v hv B T.test)
  let R := CoordinateCalibration.Multiplicity.retainedCoordinateCalibration E P hP hμ hs v hv B hCoord hGeometry C S W
    hCovariance e he rfl T hL.choose hL.choose_spec
  exact PreprimeCalibration.Intrinsic.retainedPreprimeOfCalibration E P hP hμ v hv W e he T R

end AlgebraicGeometry.HodgeConjecture.CMExtraction.PreprimeComparison.Multiplicity

namespace AlgebraicGeometry.HodgeConjecture.CMExtraction.PreprimeComparison.Intrinsic

/-! The complete AdelicTheta proposition constructs the retained nonzero test, calibrated source level, and principal depth before any prime. -/

open scoped Classical _root_.Matrix

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  {MpR MpF MpA : Type} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (Fin s × Fin 3) MpR MpF MpA)

theorem exists_retained_preprime_data (hs : 2 ≤ s)
    (hAdelicTheta : RepresentationTheory.Theta.Adelic.Data.CompleteStatement) :
    Nonempty (PreprimeCalibration.Intrinsic.RetainedPreprimeData E P hP hμ v hv W) := by
  have h := Intrinsic.OneTheta.Multiplicity.native_one_theta_from_complete_AdelicTheta E P hP hμ hs v hv hAdelicTheta
  let C := h.choose
  let hS := h.choose_spec.2.2
  let S := hS.choose
  let hB := hS.choose_spec.2.2
  let B := hB.choose
  have hp := hB.choose_spec
  exact ⟨Multiplicity.retainedPreprimeOfComparison E P hP hμ hs v hv B hp.1 hp.2.1 C S W
    hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.1⟩

end AlgebraicGeometry.HodgeConjecture.CMExtraction.PreprimeComparison.Intrinsic

end

end OAI
