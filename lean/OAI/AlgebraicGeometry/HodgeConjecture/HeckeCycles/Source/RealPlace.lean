import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RealCoefficients
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles

/-! # Real Place -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RealPlace.CM

noncomputable section

/-! The original complex inclusion determines an actual real place of
the maximal real subfield and its real completion coordinate. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.InfinitePlace _root_.NumberField.InfinitePlace.Completion
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]

def embedding : QuadraticConjugation.CM.Field.RealField E →+* ℂ := E.val.toRingHom.comp (algebraMap (QuadraticConjugation.CM.Field.RealField E) E)

def place : InfinitePlace (QuadraticConjugation.CM.Field.RealField E) := InfinitePlace.mk (embedding E)

def coordinate : (place E).Completion ≃+* ℝ :=
  ringEquivRealOfIsReal (IsTotallyReal.isReal (place E))

omit [NumberField.IsCMField E] in
theorem coordinate_continuous : Continuous (coordinate E) :=
  (isometryEquivRealOfIsReal (IsTotallyReal.isReal (place E))).continuous

omit [NumberField.IsCMField E] in
theorem real_embedding (x : QuadraticConjugation.CM.Field.RealField E) :
    (embedding_of_isReal (IsTotallyReal.isReal (place E)) x : ℂ) = embedding E x := by
  rw [embedding_of_isReal_apply]
  exact congrArg (fun f : QuadraticConjugation.CM.Field.RealField E →+* ℂ => f x)
    (InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal (embedding E)))

omit [NumberField.IsCMField E] in
theorem rational (x : QuadraticConjugation.CM.Field.RealField E) :
    (coordinate E (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (QuadraticConjugation.CM.Field.RealField E) (.inl (place E)) x) : ℂ) = (x : E).val := by
  change (extensionEmbeddingOfIsReal (IsTotallyReal.isReal (place E))
    (algebraMap (QuadraticConjugation.CM.Field.RealField E) (place E).Completion x) : ℂ) = _
  simpa [embedding, Subfield.algebraMap_ofSubfield] using real_embedding E x

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RealPlace.CM
