import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ImmersionFamily

/-! # Closed Ambient Map -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ClosedAmbientMap

noncomputable section

/-! Closed embeddings of ambient schemes carry actual native Hilbert
families to native Hilbert families over the same test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {X Y : Over S} (j : X ⟶ Y)

def ambientEmbedding (T : Over S) : Functor.ambient X T ⟶ Functor.ambient Y T :=
  (prod.map (𝟙 T) j).left

theorem ambientEmbedding_projection (T : Over S) :
    ambientEmbedding j T ≫ Functor.ambientProjection Y T = Functor.ambientProjection X T := by
  change (prod.map (𝟙 T) j).left ≫ (prod.fst : T ⨯ Y ⟶ T).left = _
  rw [← Over.comp_left, prod.map_fst, Category.comp_id]
  rfl

theorem ambientEmbedding_isPullback (T : Over S) :
    IsPullback (prod.snd : T ⨯ X ⟶ X).left (ambientEmbedding j T)
      j.left (prod.snd : T ⨯ Y ⟶ Y).left := by
  have h : IsPullback (prod.snd : T ⨯ X ⟶ X) (prod.map (𝟙 T) j) j
      (prod.snd : T ⨯ Y ⟶ Y) := by
    apply IsPullback.mk' (by simp only [prod.map_snd])
    · intro W f g hs hm
      apply prod.hom_ext
      · have h := congrArg (fun k => k ≫ (prod.fst : T ⨯ Y ⟶ T)) hm
        simpa only [Category.assoc, prod.map_fst, Category.comp_id] using h
      · exact hs
    · intro W a b hab
      refine ⟨prod.lift (b ≫ prod.fst) a, prod.lift_snd _ _, ?_⟩
      apply prod.hom_ext
      · simp only [Category.assoc, prod.map_fst, Category.comp_id, prod.lift_fst]
      · simpa only [Category.assoc, prod.map_snd, prod.lift_snd_assoc] using hab
  exact h.map (Over.forget S)

instance ambientEmbedding_isClosedImmersion [IsClosedImmersion j.left] (T : Over S) :
    IsClosedImmersion (ambientEmbedding j T) :=
  MorphismProperty.of_isPullback (ambientEmbedding_isPullback j T) inferInstance

theorem ambientEmbedding_familyProjection {T : Over S} (I : (Functor.ambient X T).IdealSheafData) :
    (I.subschemeι ≫ ambientEmbedding j T) ≫ Functor.ambientProjection Y T = Functor.familyProjection X I := by
  rw [Category.assoc, ambientEmbedding_projection]
  rfl

variable [IsClosedImmersion j.left]

def pushforwardFamily {T : Over S} (F : Functor.Family X T) : Functor.Family Y T :=
  ⟨F.val.map (ambientEmbedding j T), by
    let f := F.val.subschemeι ≫ ambientEmbedding j T
    have he : f ≫ Functor.ambientProjection Y T = Functor.familyProjection X F.val :=
      ambientEmbedding_familyProjection j F.val
    let : Flat (f ≫ Functor.ambientProjection Y T) := he.symm ▸ F.property.1
    let : IsProper (f ≫ Functor.ambientProjection Y T) := he.symm ▸ F.property.2.1
    let : LocallyOfFinitePresentation (f ≫ Functor.ambientProjection Y T) := he.symm ▸ F.property.2.2
    exact Closed.ImmersionFamily.Hilbert.closedImmersion_isFamily Y f⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ClosedAmbientMap
