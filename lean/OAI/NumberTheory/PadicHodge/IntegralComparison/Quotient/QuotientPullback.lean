import Mathlib

/-! # Quotient Pullback -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.QuotientPullback

noncomputable section

/-!
# IntegralComparison: base change of an affine closed subscheme

For an arbitrary ring map A → S, the closed subscheme defined by the
extended ideal IS is the scheme-theoretic pullback of Spec(A/I).
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {A S : Type u} [CommRing A] [CommRing S] (I : Ideal A) (f : A →+* S)

def residueMap : A ⧸ I →+* S ⧸ I.map f :=
  Ideal.quotientMap (I.map f) f (Ideal.le_comap_map)

lemma residueMap_comp : (residueMap I f).comp (Ideal.Quotient.mk I) =
    (Ideal.Quotient.mk (I.map f)).comp f := rfl

def quotientCocone : PushoutCocone (CommRingCat.ofHom f)
    (CommRingCat.ofHom (Ideal.Quotient.mk I)) :=
  PushoutCocone.mk (CommRingCat.ofHom (Ideal.Quotient.mk (I.map f)))
    (CommRingCat.ofHom (residueMap I f)) rfl

private lemma cocone_kills (s : PushoutCocone (CommRingCat.ofHom f)
    (CommRingCat.ofHom (Ideal.Quotient.mk I))) : I.map f ≤ RingHom.ker s.inl.hom := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  change s.inl.hom (f a) = 0
  have he := congrArg (fun t : CommRingCat.of A ⟶ s.pt => t.hom a) s.condition
  change s.inl.hom (f a) = s.inr.hom (Ideal.Quotient.mk I a) at he
  rw [he, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

def quotientCoconeIsColimit : IsColimit (quotientCocone I f) :=
  PushoutCocone.isColimitAux' _ fun s => by
    let d := CommRingCat.ofHom (Ideal.Quotient.lift (I.map f) s.inl.hom (cocone_kills I f s))
    refine ⟨d, ?_, ?_, ?_⟩
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      rfl
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact congrArg (fun t : CommRingCat.of A ⟶ s.pt => t.hom a) s.condition
    · intro m hm _
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact congrArg (fun t : CommRingCat.of S ⟶ s.pt => t.hom a) hm

lemma ringPushout : IsPushout (CommRingCat.ofHom f)
    (CommRingCat.ofHom (Ideal.Quotient.mk I))
    (CommRingCat.ofHom (Ideal.Quotient.mk (I.map f))) (CommRingCat.ofHom (residueMap I f)) where
  w := rfl
  isColimit' := ⟨quotientCoconeIsColimit I f⟩

lemma schemePullback :
    IsPullback (Spec.map (CommRingCat.ofHom (residueMap I f)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map f))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) (Spec.map (CommRingCat.ofHom f)) :=
  (ringPushout I f).op.map Scheme.Spec

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.QuotientPullback
