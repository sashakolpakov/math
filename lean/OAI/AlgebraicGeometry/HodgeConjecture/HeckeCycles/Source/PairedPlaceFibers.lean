import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PadicEmbeddingPlace
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicPlace

/-! # Paired Place Fibers -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PairedPlaceFibers.CM

noncomputable section

section

/-! The two q-adic CM embeddings over a fixed real-subfield place are
exactly a conjugate pair, in the actual source field coordinates. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QadicPlace.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {q : ℕ} [Fact q.Prime] (f g : E →+* ℚ_[q])

include Q in
theorem embeddings_eq_or_conjugate (h : QadicPlace.CM.realEmbedding E f = QadicPlace.CM.realEmbedding E g) :
    f = g ∨ f = g.comp (NumberField.IsCMField.complexConj E).toRingHom := by
  have hreal (a : QuadraticConjugation.CM.Field.RealField E) : f (a : E) = g (a : E) := RingHom.congr_fun h a
  have hs : f Q.delta ^ 2 = g Q.delta ^ 2 := by
    rw [← map_pow, ← map_pow]
    exact hreal (QuadraticConjugation.CM.Field.discriminant E Q)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hs | hs
  · left
    ext x
    obtain ⟨z, rfl⟩ := (QuadraticConjugation.CM.Field.fieldEquiv E Q).surjective x
    change f (QuadraticConjugation.CM.Field.toOriginal E Q z) = g (QuadraticConjugation.CM.Field.toOriginal E Q z)
    rw [QuadraticConjugation.CM.Field.toOriginal_apply, map_add, map_mul, map_add, map_mul, hreal, hreal, hs]
  · right
    ext x
    obtain ⟨z, rfl⟩ := (QuadraticConjugation.CM.Field.fieldEquiv E Q).surjective x
    change f (QuadraticConjugation.CM.Field.toOriginal E Q z) = g (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (QuadraticConjugation.CM.Field.toOriginal E Q z))
    rw [QuadraticConjugation.CM.Field.toOriginal_apply, map_add, map_mul, map_add, map_mul,
      QuadraticConjugation.CM.real_fixed, QuadraticConjugation.CM.real_fixed,
      Q.delta_imaginary, map_add, map_mul, map_neg, hreal, hreal, hs]

theorem place_conjugate :
    QadicPlace.CM.place E (f.comp (NumberField.IsCMField.complexConj E).toRingHom) = QadicPlace.CM.place E f := by
  apply congrArg PELModuli.CMPoints.LocalPadic.embeddingPlace
  ext x
  change f (NumberField.IsCMField.complexConj E (x : E)) = f (x : E)
  rw [NumberField.IsCMField.complexConj_apply_eq_self]

include Q in
theorem place_eq_iff : QadicPlace.CM.place E f = QadicPlace.CM.place E g ↔
    f = g ∨ f = g.comp (NumberField.IsCMField.complexConj E).toRingHom := by
  constructor
  · intro h
    exact embeddings_eq_or_conjugate E Q f g
      (PadicEmbeddingPlace.CM.padic_embeddingPlace_injective (QuadraticConjugation.CM.Field.RealField E) h)
  · rintro (h | h)
    · exact congrArg (QadicPlace.CM.place E) h
    · rw [h, place_conjugate]

end

/-! Injective conjugate-paired q-adic labels have exactly one pair over
each real-subfield place. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (Q : GeometricSource.CM.SymplecticCoordinates E B places)
  {q : ℕ} [Fact q.Prime] {I : Type*} (τ : I × Bool → E →+* ℚ_[q])
  (hinj : Function.Injective τ)
  (hconj : ∀ i b, τ (i, !b) = (τ (i, b)).comp (NumberField.IsCMField.complexConj E).toRingHom)

include Q hinj hconj in
theorem fiber (i j : I × Bool) :
    QadicPlace.CM.place E (τ i) = QadicPlace.CM.place E (τ j) ↔ i.1 = j.1 := by
  constructor
  · intro h
    rcases (place_eq_iff E Q (τ i) (τ j)).mp h with he | he
    · exact congrArg Prod.fst (hinj he)
    · have he' : τ i = τ (j.1, !j.2) := he.trans (hconj j.1 j.2).symm
      have hi : i = (j.1, !j.2) := hinj he'
      have hip := congrArg (fun k : I × Bool => k.1) hi
      exact hip
  · rcases i with ⟨i, a⟩
    rcases j with ⟨j, b⟩
    intro h
    change i = j at h
    subst j
    have hc (side : Bool) :
        QadicPlace.CM.place E (τ (i, !side)) = QadicPlace.CM.place E (τ (i, side)) := by
      rw [hconj, place_conjugate]
    cases a <;> cases b
    · rfl
    · exact hc true
    · exact hc false
    · rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PairedPlaceFibers.CM
