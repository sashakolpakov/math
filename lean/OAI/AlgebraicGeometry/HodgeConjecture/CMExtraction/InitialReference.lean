import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.InitialPlaceNumbering
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELDatum

/-! # Initial Reference -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.InitialReference.Intrinsic

noncomputable section

/-! Construct an admissible PEL reference with the source's active pair
numbered zero. This choice precedes the retained test, level, and prime. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]

omit [IsGalois ℚ E] in
theorem source_places_at_least_two (B : HeckeCycles.GeometricSource.CM.BallDatum E) (places : HeckeCycles.GeometricSource.CM.Places E) :
    2 ≤ places.count := by
  by_contra hcount
  obtain ⟨τ, hτ, hc⟩ := B.other_place
  obtain ⟨⟨i, b⟩, hi⟩ := places.complete.2 τ
  have he : i = places.distinguished := Fin.ext (by
    have hi := i.isLt
    have hd := places.distinguished.isLt
    omega)
  subst i
  cases b with
  | false =>
      simp only [Bool.false_eq_true, ite_false, places.identity] at hi
      exact hτ hi.symm
  | true =>
      simp only [ite_true, places.identity, mul_one] at hi
      exact hc hi.symm

theorem initial_reference_with_active_zero
    (B : HeckeCycles.GeometricSource.CM.BallDatum E) (places : HeckeCycles.GeometricSource.CM.Places E) (hCongruenceLevel : HeckeCycles.ReferenceDatum.CM.CongruenceLevelInput E places.count)
    (dref : Fin places.count → Bool) :
    ∃ P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E places.count,
      P.IsAdmissible ∧ P.μ = E.val.toRingHom ∧ P.b = B.b ∧
      P.distinguished.val = 0 ∧
      (∀ i, P.embeddings i = HeckeCycles.ReferenceDatum.CM.embeddings E places (InitialPlaceNumbering.Intrinsic.initialPlacePermutation E places i)) ∧
      P.compactSigns = dref ∘ InitialPlaceNumbering.Intrinsic.initialPlacePermutation E places := by
  obtain ⟨P, hP, hb, hemb, ha, hd⟩ := HeckeCycles.PELDatum.CM.admissible_reference_datum E B
    (InitialPlaceNumbering.Intrinsic.activeFirstPlaces E places) hCongruenceLevel (dref ∘ InitialPlaceNumbering.Intrinsic.initialPlacePermutation E places)
  refine ⟨P, hP, ?_, hb, ?_, ?_, hd⟩
  · change (P.embeddings P.distinguished).toRingHom = E.val.toRingHom
    rw [hemb, ha, HeckeCycles.ReferenceDatum.CM.embeddings_distinguished]
  · rw [ha]
    exact InitialPlaceNumbering.Intrinsic.activeFirstPlaces_active E places
  · intro i
    rw [hemb]
    rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.InitialReference.Intrinsic
