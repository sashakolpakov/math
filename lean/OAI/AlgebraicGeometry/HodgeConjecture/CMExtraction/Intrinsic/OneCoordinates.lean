import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OneTheta
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneIndex
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneUnitary

/-! # One Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OneCoordinates.Multiplicity

noncomputable section

/-! The same AdelicTheta witnesses furnish the native rational symplectic
coordinates and the original CM embedding and sign labels. -/

open scoped Classical _root_.NumberField
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (hs : 2 ≤ s) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)

theorem nativeOneBall_sign (i : Fin s) :
    (OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv).positive i 0 = !(Multiplicity.Period.nativeCompactSigns E P v i) := by
  change decide (0 < 2 * (HeckeCycles.ReferenceDatum.CM.embeddings E
    (Representatives.Multiplicity.nativePlaces E P hP hμ) i (P.imaginaryScalar * Multiplicity.nativeCoefficient E P v)).im) = _
  have hsign := (mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)
    (b := (HeckeCycles.ReferenceDatum.CM.embeddings E
      (Representatives.Multiplicity.nativePlaces E P hP hμ) i (P.imaginaryScalar * Multiplicity.nativeCoefficient E P v)).im)).trans
        (IntrinsicOne.Multiplicity.native_single_skew_sign E P hP hμ v i)
  cases hd : Multiplicity.Period.nativeCompactSigns E P v i
  · exact decide_eq_true (hsign.mpr hd)
  · apply decide_eq_false
    intro hp
    exact Bool.noConfusion (hd.symm.trans (hsign.mp hp))

theorem nativeOneBall_embedding (i : Fin s)
    (x : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield E) (OneTheta.Multiplicity.nativeOneParameter E P hP)) :
    (OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv).complex i
      (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (maximalRealSubfield E) (OneTheta.Multiplicity.nativeOneParameter E P hP)
        (.inl ((OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv).enumerate i)) x) =
      P.embeddings i (ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E P.imaginaryScalar (OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
        (OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) x) := by
  exact (ThetaCycle.CMArchimedeanCoordinates.CM.source_complex_coordinate_rational E (Representatives.Multiplicity.nativePlaces E P hP hμ)
    P.imaginaryScalar (OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP) (OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) i x).trans
      (congrArg (fun f : E →ₐ[ℚ] ℂ => f _) (IntrinsicOne.Multiplicity.nativePlaces_embeddings E P hP hμ i))

variable (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData (maximalRealSubfield E) (OneTheta.Multiplicity.nativeOneHermitian E P hP)
  (OneTheta.Multiplicity.nativeOneSkew E P hP v) (OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv))

def nativeOneRationalCoordinates :
    (Fin 3 → E) ≃ₗ[ℚ] ((Sum (Fin s × Fin 3) (Fin s × Fin 3)) → ℚ) :=
  Multiplicity.OneIndex.Quadratic.flattenedRationalCoordinates E P.imaginaryScalar (OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
    (OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) P.b hP.2.1 hP.2.2.1
    (Multiplicity.nativeCoefficient E P v) (Multiplicity.nativeCoefficient_real E P hP v)
    (Multiplicity.nativeCoefficient_ne_zero E P hP v) (OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv) B

theorem nativeOneRationalCoordinates_pairing
    (hCoord : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification B (OneTheta.Multiplicity.nativeOneFrames E P hP v))
    (x y : Fin 3 → E) :
    RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing
      (nativeOneRationalCoordinates E P hP hμ hs v hv B x)
      (nativeOneRationalCoordinates E P hP hμ hs v hv B y) =
      Algebra.trace ℚ E (P.imaginaryScalar * Multiplicity.nativeTensorPairing E P v x y) :=
  Multiplicity.OneIndex.Quadratic.flattenedRationalCoordinates_pairing E P.imaginaryScalar (OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
    (OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) P.b hP.2.1 hP.2.2.1
    (Multiplicity.nativeCoefficient E P v) (Multiplicity.nativeCoefficient_real E P hP v)
    (Multiplicity.nativeCoefficient_ne_zero E P hP v) (OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv) B hCoord x y

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OneCoordinates.Multiplicity
