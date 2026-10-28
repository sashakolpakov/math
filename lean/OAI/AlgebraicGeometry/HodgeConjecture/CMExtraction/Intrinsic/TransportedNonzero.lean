import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.TransportedForm
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NonzeroTest

/-! # Transported Nonzero -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.TransportedNonzero

noncomputable section

/-! The same native test selected before the prime remains nonzero in
the actual AdelicTheta one-form construction. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (hs : 2 ≤ s) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData (maximalRealSubfield E) (OneTheta.Multiplicity.nativeOneHermitian E P hP)
    (OneTheta.Multiplicity.nativeOneSkew E P hP v) (OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv))

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

theorem native_retained_test_comparison_value
    (hCoord : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification B (OneTheta.Multiplicity.nativeOneFrames E P hP v))
    (hGeometry : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification B)
    (T : NonzeroTest.NativeThetaTest E P hP hμ v hv
      (OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B)
      (OneCoordinates.Multiplicity.nativeOneRationalCoordinates_pairing E P hP hμ hs v hv B hCoord)) :
    RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B (TransportedForm.Multiplicity.nativeOneFiniteTest E P hP hμ hs v hv B T.test)
        (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ (PeriodDomain.Multiplicity.nativeOrigin E P hP)) (Pi.single 0 1) =
      TransportedForm.Multiplicity.nativeOneThetaFactor E P hP hμ hs v hv B hCoord := by
  rw [TransportedForm.Multiplicity.nativeOneFiniteTest_thetaOneForm E P hP hμ hs v hv B hCoord hGeometry,
    smul_apply, T.value, smul_eq_mul, mul_one]

theorem native_retained_test_comparison_nonzero
    (hCoord : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification B (OneTheta.Multiplicity.nativeOneFrames E P hP v))
    (hGeometry : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification B)
    (T : NonzeroTest.NativeThetaTest E P hP hμ v hv
      (OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B)
      (OneCoordinates.Multiplicity.nativeOneRationalCoordinates_pairing E P hP hμ hs v hv B hCoord)) :
    RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B (TransportedForm.Multiplicity.nativeOneFiniteTest E P hP hμ hs v hv B T.test)
        (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ (PeriodDomain.Multiplicity.nativeOrigin E P hP)) (Pi.single 0 1) ≠ 0 := by
  rw [native_retained_test_comparison_value E P hP hμ hs v hv B hCoord hGeometry T]
  exact TransportedForm.Multiplicity.nativeOneThetaFactor_ne_zero E P hP hμ hs v hv B hCoord hGeometry

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.TransportedNonzero
