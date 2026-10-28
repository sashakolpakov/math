import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FilledLocal
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QuadraticScalarSupport
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LinearMatrixSupport
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalPrimeSupport

/-! # Filled Support -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FilledSupport.CM

noncomputable section

/-! Removing the source active factor changes the PEL operator only at
its rational prime. Every other rational-prime coordinate is unchanged. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalPrimeSupport.TestTransport
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ScalarEmbedding.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QuadraticScalarSupport.CM

theorem idempotent_at_split (F : Type) [Field F] [NumberField F]
    {q : ℕ} [Fact q.Prime] (f : F →+* ℚ_[q]) :
    Adelic.ScalarEmbedding.CM.adelicScalarEmbedding F (CMExtraction.RationalPrimeSupport.TestTransport.rationalPrimeIdempotent q) (PELModuli.CMPoints.LocalPadic.embeddingPlace f) = 1 := by
  apply (PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv f).injective
  exact (Adelic.ScalarEmbedding.CM.adelicScalarEmbedding_at_split F f (CMExtraction.RationalPrimeSupport.TestTransport.rationalPrimeIdempotent q)).trans
    ((CMExtraction.RationalPrimeSupport.TestTransport.rationalPrimeIdempotent_same q).trans (map_one _).symm)

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hb : P.b = B.b)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

theorem coefficient_support (g : SourceFinite.Product.CM.FiniteGroup E Q) (i j : Fin 3) :
    CMExtraction.RationalPrimeSupport.TestTransport.rationalPrimeIdempotent q •
      (PELScalar.CM.equivalence E Q
        (CMExtraction.Finite.UnitaryDet.Approximation.finiteSUQuadraticMatrix (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q) (FilledLocal.CM.PEL.fill E Q f g) i j) -
       PELScalar.CM.equivalence E Q
        (CMExtraction.Finite.UnitaryDet.Approximation.finiteSUQuadraticMatrix (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q) g i j)) =
      PELScalar.CM.equivalence E Q
        (CMExtraction.Finite.UnitaryDet.Approximation.finiteSUQuadraticMatrix (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q) (FilledLocal.CM.PEL.fill E Q f g) i j) -
       PELScalar.CM.equivalence E Q
        (CMExtraction.Finite.UnitaryDet.Approximation.finiteSUQuadraticMatrix (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q) g i j) := by
  exact QuadraticScalarSupport.CM.quadraticAdelicTensorMap_sub_support (QuadraticConjugation.CM.Field.discriminant E Q) (QuadraticConjugation.CM.Field.fieldEquiv E Q)
    (CMExtraction.RationalPrimeSupport.TestTransport.rationalPrimeIdempotent q) _ _
    (QuadraticScalarSupport.CM.finiteSU_difference_supported (QuadraticConjugation.CM.Field.RealField E) (QuadraticForms.CM.hermitianForm E Q)
      (QadicPlace.CM.place E f) g (FilledLocal.CM.PEL.fill E Q f g)
      (fun _ hw => RestrictedFillComparison.CM.other (SourceFinite.Product.CM.levels E Q)
        (QadicPlace.CM.place E f) g hw) _
      (idempotent_at_split (QuadraticConjugation.CM.Field.RealField E) (QadicPlace.CM.realEmbedding E f)) i j)

theorem matrix_support (g : SourceFinite.Product.CM.FiniteGroup E Q) (i j : Fin 3) :
    CMExtraction.RationalPrimeSupport.TestTransport.rationalPrimeIdempotent q •
      ((PELFiniteGroup.CM.pel E Q P hb (FilledLocal.CM.PEL.fill E Q f g)).val (Pi.single j 1) i -
       (PELFiniteGroup.CM.pel E Q P hb g).val (Pi.single j 1) i) =
      (PELFiniteGroup.CM.pel E Q P hb (FilledLocal.CM.PEL.fill E Q f g)).val (Pi.single j 1) i -
       (PELFiniteGroup.CM.pel E Q P hb g).val (Pi.single j 1) i := by
  have he := (PELFiniteGroup.CM.Matrix.entry E Q P hb g i j).trans
    (congrArg (fun M : Matrix (Fin 3) (Fin 3) (AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) => M i j)
      (PELFiniteGroup.CM.matrix E Q g))
  exact Eq.mpr (congrArg₂ (fun x y : AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E =>
    CMExtraction.RationalPrimeSupport.TestTransport.rationalPrimeIdempotent q • (x - y) = x - y)
    (FilledLocal.CM.PEL.matrix_entry E Q P hb f g i j) he)
      (coefficient_support E Q f g i j)

theorem other_coordinate (g : SourceFinite.Product.CM.FiniteGroup E Q)
    (x : Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E)
    (c : (Fin 3 → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) →ₗ[AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles] AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles)
    (p : ℕ) [Fact p.Prime] (hpq : p ≠ q) :
    RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p
      (c ((PELFiniteGroup.CM.pel E Q P hb (FilledLocal.CM.PEL.fill E Q f g)).val x)) =
    RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p
      (c ((PELFiniteGroup.CM.pel E Q P hb g).val x)) :=
  CMExtraction.RationalPrimeSupport.TestTransport.supported_linear_difference q p hpq c _ _
    (LinearMatrixSupport.CM.apply (CMExtraction.RationalPrimeSupport.TestTransport.rationalPrimeIdempotent q) _ _
      (matrix_support E Q P hb f g) x)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FilledSupport.CM
