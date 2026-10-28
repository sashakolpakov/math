import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.PELId
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntegralAdded.FineBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.GenericReduced
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.BaseChange

/-! # Added Generic Family -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual generic two-level family with exactly the coefficient
embedding of ReferenceFamily's base-changed reference universal family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {κ : K →+* ℂ} (B : Base.ArithmeticBaseExtension K κ)
    {s p N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} (iota : E →+* K)
    {V : Over B.base}

omit [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] in
theorem Arithmetic.AddedGenericFamily.arithmetic_generic_reference_embedding :
    B.toField.comp (B.integralEmbedding iota) =
      (algebraMap K B.extension.carrier).comp
        (iota.comp (algebraMap (NumberField.RingOfIntegers E) E)) := by
  ext a
  exact B.integralEmbedding_toField iota a

def IntegralAdded.PELId.IntegralAddedPELLevel.genericIntegralFamily
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N V) :
    IntegralAdded.PELId.IntegralAddedPELLevel P B.extension.carrier
      ((algebraMap K B.extension.carrier).comp
        (iota.comp (algebraMap (NumberField.RingOfIntegers E) E))) p N
      ((Over.pullback B.generic).obj V) :=
  (U.baseChange B.toField).changeEmbedding (Arithmetic.AddedGenericFamily.arithmetic_generic_reference_embedding B iota)

theorem Arithmetic.AddedGenericFamily.arithmetic_addedPEL_generic_classifies
    (U : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N V)
    (hclass : ∀ (T : Over B.base) [IsReduced T.left]
      (A : IntegralAdded.PELId.IntegralAddedPELLevel P B.R (B.integralEmbedding iota) p N T),
      ∃! f : T ⟶ V, Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso (U.pullback f) A))
    (T : Over (Spec (.of B.extension.carrier))) [IsReduced T.left]
    (A : IntegralAdded.PELId.IntegralAddedPELLevel P B.extension.carrier
      ((algebraMap K B.extension.carrier).comp
        (iota.comp (algebraMap (NumberField.RingOfIntegers E) E))) p N T) :
    ∃! f : T ⟶ (Over.pullback B.generic).obj V,
      Nonempty (IntegralAdded.PELId.IntegralAddedPELLevel.Iso ((U.genericIntegralFamily B iota).pullback f) A) :=
  IntegralAdded.PELId.integralAddedPEL_fine_changeEmbedding (U.baseChange B.toField)
    (Arithmetic.AddedGenericFamily.arithmetic_generic_reference_embedding B iota)
    (IntegralAdded.FineBaseChange.integralAddedPEL_fine_baseChange U hclass B.toField) T A

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
