import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.TransportedNonzero
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SingleTestOpenLevel

/-! # Transported Level -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.TransportedLevel

noncomputable section

/-! A compact open source level for the same retained native test is
constructed before choosing the finite prime. Its principal congruence
and torsion-freeness properties come from the full AdelicTheta conclusion. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary
open OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SingleTestOpenLevel.Transport

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (hs : 2 ≤ s) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData (maximalRealSubfield E) (OneTheta.Multiplicity.nativeOneHermitian E P hP)
    (OneTheta.Multiplicity.nativeOneSkew E P hP v) (OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv))
  (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters (maximalRealSubfield E) (OneTheta.Multiplicity.nativeOneParameter E P hP) 3 1)
  (D : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings (maximalRealSubfield E) (OneTheta.Multiplicity.nativeOneParameter E P hP) 3 1
    (OneTheta.Multiplicity.nativeOneHermitian E P hP) (OneTheta.Multiplicity.nativeOneSkew E P hP v) (OneTheta.Multiplicity.nativeOneParameterNonzero E P hP)
    C (OneTheta.Multiplicity.nativeOneFrames E P hP v))

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

theorem exists_native_retained_comparison_level
    (hCoord : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification B (OneTheta.Multiplicity.nativeOneFrames E P hP v))
    (hGeometry : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification B)
    (hDescent : RepresentationTheory.Theta.Adelic.DataTheta.Descent.CongruenceDescent B (OneTheta.Multiplicity.nativeOneFrames E P hP v)
      (OneTheta.Multiplicity.nativeOneParameterNonzero E P hP) C D)
    (T : NonzeroTest.NativeThetaTest E P hP hμ v hv
      (OneCoordinates.Multiplicity.nativeOneRationalCoordinates E P hP hμ hs v hv B)
      (OneCoordinates.Multiplicity.nativeOneRationalCoordinates_pairing E P hP hμ hs v hv B hCoord))
    (K₀ : OpenSubgroup (RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (maximalRealSubfield E) (OneTheta.Multiplicity.nativeOneHermitian E P hP)))
    (N₀ : ℕ) (hN₀ : 0 < N₀) :
    SingleTestOpenLevel.Transport.SingleTestLevel (OneTheta.Multiplicity.nativeOneFrames E P hP v) (OneTheta.Multiplicity.nativeOneParameterNonzero E P hP) C D
      (TransportedForm.Multiplicity.nativeOneFiniteTest E P hP hμ hs v hv B T.test) K₀ N₀ ∧
      RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection.thetaOneForm B (TransportedForm.Multiplicity.nativeOneFiniteTest E P hP hμ hs v hv B T.test)
        (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ (PeriodDomain.Multiplicity.nativeOrigin E P hP)) (Pi.single 0 1) ≠ 0 := by
  exact ⟨SingleTestOpenLevel.Transport.single_test_level_from_descent (OneTheta.Multiplicity.nativeOneFrames E P hP v)
    (OneTheta.Multiplicity.nativeOneParameterNonzero E P hP) C D B hDescent
    (TransportedForm.Multiplicity.nativeOneFiniteTest E P hP hμ hs v hv B T.test) K₀ N₀ hN₀,
    TransportedNonzero.native_retained_test_comparison_nonzero E P hP hμ hs v hv B hCoord hGeometry T⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.TransportedLevel
