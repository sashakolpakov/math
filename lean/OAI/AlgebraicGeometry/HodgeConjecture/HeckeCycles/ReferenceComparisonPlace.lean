import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalEmbedding
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ParameterChoices
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap

/-! # Reference Comparison Place -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceComparisonPlace.CM.Reference

/-! The original ordinary comparison embedding has the conjugate
restriction required to transport the source parameter valuations.
This follows from its actual integral active character. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)

theorem field_embedding (w : Fin s × Bool) (τ : Gal(E/ℚ))
    (hχ : D.localCharacter w = j.localCharacter D.fieldEmbedding τ) :
    CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D w = (QadicModelMap.CM.localFieldEmbedding j).comp (D.fieldEmbedding.comp τ.toRingHom) := by
  apply IsFractionRing.ringHom_ext (A := NumberField.RingOfIntegers E)
  intro a
  exact (CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding_onIntegers D w a).trans
    ((congrArg (fun χ : NumberField.RingOfIntegers E →+* ℤ_[q] => (χ a : ℚ_[q])) hχ).trans
      (RingHom.congr_fun j.integral_compatibility
        (NumberField.RingOfIntegers.mapRingHom (D.fieldEmbedding.comp τ.toRingHom) a)))

theorem opposite_field
    (hχ : D.localCharacter (D.reference.distinguished, false) =
      j.localCharacter D.fieldEmbedding (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)) (x : E) :
    QadicModelMap.CM.localFieldEmbedding j (D.fieldEmbedding x) =
      CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E x) := by
  have h := RingHom.congr_fun (field_embedding E D j (D.reference.distinguished, false) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E) hχ)
    (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E x)
  change CMExtraction.LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E x) =
    QadicModelMap.CM.localFieldEmbedding j (D.fieldEmbedding (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E x))) at h
  simpa only [ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_apply_apply] using h.symm

theorem closure_restriction (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar)
    (hιE : ιE.toRingHom = j.fieldInClosure.comp D.fieldEmbedding)
    (hχ : D.localCharacter (D.reference.distinguished, false) =
      j.localCharacter D.fieldEmbedding (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)) (x : E) :
    j.iota (ιE x) = CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)
      (ιE (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E x)) := by
  exact (congrArg j.iota (RingHom.congr_fun hιE x)).trans
    ((RingHom.congr_fun j.closure_compatibility (D.fieldEmbedding x)).trans
      ((congrArg (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])) (opposite_field E D j hχ x)).trans
        (CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding_spec D ιE (D.reference.distinguished, false) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E x)).symm))

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceComparisonPlace.CM.Reference

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceComparisonPlace.CM.SourceClosureChoice

/-! Use the coefficient-field embedding into the algebraic closure
already determined by the original ordinary comparison place. -/

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)

def embedding : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar := (j.fieldInClosure.comp D.fieldEmbedding).toRatAlgHom

theorem underlying : (SourceClosureChoice.embedding E D j).toRingHom = j.fieldInClosure.comp D.fieldEmbedding := rfl

theorem complex_compatibility (hg : D.HasIntegralModelGeometry) (hμ : D.reference.μ = E.val.toRingHom)
    (x : E) : j.complexClosure (SourceClosureChoice.embedding E D j x) = (x : ℂ) := by
  exact (RingHom.congr_fun j.complex_compatibility (D.fieldEmbedding x)).trans
    ((RingHom.congr_fun hg.embedding x).trans (RingHom.congr_fun hμ x))

theorem local_restriction
    (hχ : D.localCharacter (D.reference.distinguished, false) =
      j.localCharacter D.fieldEmbedding (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)) (x : E) :
    j.iota (SourceClosureChoice.embedding E D j x) =
      CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D (SourceClosureChoice.embedding E D j) (D.reference.distinguished, false)
        (SourceClosureChoice.embedding E D j (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E x)) :=
  Reference.closure_restriction E D j (SourceClosureChoice.embedding E D j) rfl hχ x

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceComparisonPlace.CM.SourceClosureChoice

end

end OAI
