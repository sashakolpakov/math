import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.TransportedLevel
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SingleTestOpenLevel
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.FiniteAway

/-! # Source Test Open Level -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SourceTestOpenLevel.Multiplicity

noncomputable section

/-! A source open subgroup fixing the specified native AdelicTheta test. -/

open scoped Classical _root_.Matrix _root_.NumberField
open _root_.Matrix _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.TransportedLevel OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SingleTestOpenLevel.Transport OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates
open OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicCovariance OAI.RepresentationTheory.Theta.OneFormsIntrinsicLattice.IntrinsicProjection

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (hs : 2 ≤ s) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData (maximalRealSubfield E) (OneTheta.Multiplicity.nativeOneHermitian E P hP)
    (OneTheta.Multiplicity.nativeOneSkew E P hP v) (OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv))
  (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters (maximalRealSubfield E) (OneTheta.Multiplicity.nativeOneParameter E P hP) 3 1)
  (S : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings (maximalRealSubfield E) (OneTheta.Multiplicity.nativeOneParameter E P hP) 3 1
    (OneTheta.Multiplicity.nativeOneHermitian E P hP) (OneTheta.Multiplicity.nativeOneSkew E P hP v) (OneTheta.Multiplicity.nativeOneParameterNonzero E P hP)
    C (OneTheta.Multiplicity.nativeOneFrames E P hP v))

theorem exists_native_source_test_level
    (hDescent : RepresentationTheory.Theta.Adelic.DataTheta.Descent.CongruenceDescent B (OneTheta.Multiplicity.nativeOneFrames E P hP v)
      (OneTheta.Multiplicity.nativeOneParameterNonzero E P hP) C S)
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (maximalRealSubfield E) (3 * 1)) :
    ∃ L : OpenSubgroup (CM.FiniteAway.Approximation.CMFiniteSU E P hP), ∀ g ∈ L,
      RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteAction (maximalRealSubfield E) (OneTheta.Multiplicity.nativeOneHermitian E P hP)
        (OneTheta.Multiplicity.nativeOneSkew E P hP v) (OneTheta.Multiplicity.nativeOneParameterNonzero E P hP) C
          (OneTheta.Multiplicity.nativeOneFrames E P hP v) S g f = f :=
  SingleTestOpenLevel.Transport.exists_single_test_open_level (OneTheta.Multiplicity.nativeOneFrames E P hP v) (OneTheta.Multiplicity.nativeOneParameterNonzero E P hP)
    C S B hDescent f

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SourceTestOpenLevel.Multiplicity
