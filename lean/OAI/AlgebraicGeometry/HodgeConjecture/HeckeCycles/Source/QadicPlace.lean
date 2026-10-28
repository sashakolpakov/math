import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RationalLocal
import OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalPadic

/-! # Qadic Place -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicPlace.CM

noncomputable section

/-! A prescribed q-adic embedding constructs the actual place of the
source's real subfield, its completion, and its quadratic splitting root. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {q : ℕ} [Fact q.Prime] (f : E →+* ℚ_[q])

def realEmbedding : QuadraticConjugation.CM.Field.RealField E →+* ℚ_[q] := f.comp (algebraMap (QuadraticConjugation.CM.Field.RealField E) E)

def place : IsDedekindDomain.HeightOneSpectrum (𝓞 (QuadraticConjugation.CM.Field.RealField E)) :=
  PELModuli.CMPoints.LocalPadic.embeddingPlace (realEmbedding E f)

def completionEquiv : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion (QuadraticConjugation.CM.Field.RealField E) (.inr (place E f)) ≃+* ℚ_[q] :=
  PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv (realEmbedding E f)

omit [NumberField.IsCMField E] in
theorem completion_continuous : Continuous (completionEquiv E f) :=
  PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv_continuous (realEmbedding E f)

omit [NumberField.IsCMField E] in
theorem completion_inverse_continuous : Continuous (completionEquiv E f).symm :=
  PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv_symm_continuous (realEmbedding E f)

omit [NumberField.IsCMField E] in
theorem completion_rational (x : QuadraticConjugation.CM.Field.RealField E) :
    completionEquiv E f (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (QuadraticConjugation.CM.Field.RealField E) (.inr (place E f)) x) = realEmbedding E f x :=
  PELModuli.CMPoints.LocalPadic.embeddingCompletionHom_coe (realEmbedding E f) x

def root : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion (QuadraticConjugation.CM.Field.RealField E) (.inr (place E f)) := (completionEquiv E f).symm (f Q.delta)

theorem root_sq : (root E Q f) ^ 2 = RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (QuadraticConjugation.CM.Field.RealField E) (.inr (place E f)) (QuadraticConjugation.CM.Field.discriminant E Q) := by
  apply (completionEquiv E f).injective
  rw [map_pow, completion_rational]
  change ((completionEquiv E f) ((completionEquiv E f).symm (f Q.delta))) ^ 2 = f (Q.delta ^ 2)
  rw [RingEquiv.apply_symm_apply, map_pow]

theorem root_ne_zero : root E Q f ≠ 0 := by
  intro h
  have he := congrArg (completionEquiv E f) h
  change completionEquiv E f ((completionEquiv E f).symm (f Q.delta)) = completionEquiv E f 0 at he
  rw [RingEquiv.apply_symm_apply, map_zero] at he
  exact Q.delta_ne_zero (f.injective (he.trans f.map_zero.symm))

theorem root_image : completionEquiv E f (root E Q f) = f Q.delta :=
  (completionEquiv E f).apply_symm_apply _

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicPlace.CM
