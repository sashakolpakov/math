import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleReduced
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverEffectiveDescent
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Etale Quotient Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleQuotientComparison

noncomputable section

/-! Two finite etale quotients with the same fibers on reduced test
schemes are canonically isomorphic. Reducedness of their actual kernel
pairs is proved, so arbitrary nonreduced tests are also accounted for. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {S : Scheme.{0}} {X Y Z : Over S} [IsReduced X.left]

theorem finite_etale_factor_of_reduced_fibers (p : X ⟶ Y)
    [IsFinite p.left] [Etale p.left] [Surjective p.left] (q : X ⟶ Z)
    (h : ∀ (T : Over S) [IsReduced T.left] (a b : T ⟶ X),
      a ≫ p = b ≫ p → a ≫ q = b ≫ q) :
    ∃! d : Y ⟶ Z, p ≫ d = q := by
  have hs := (IsPullback.of_hasPullback p p).map (Over.forget S)
  have : IsFinite (pullback.fst p p).left :=
    MorphismProperty.of_isPullback hs.flip (inferInstanceAs (IsFinite p.left))
  have : Etale (pullback.fst p p).left :=
    MorphismProperty.of_isPullback hs.flip (inferInstanceAs (Etale p.left))
  have : IsReduced (pullback p p).left := EtaleReduced.finite_etale_isReduced (pullback.fst p p).left
  have he := h (pullback p p) (pullback.fst p p) (pullback.snd p p) pullback.condition
  apply OverEffectiveDescent.over_factor_of_effectiveEpi p q
  intro T a b hab
  have hh := congrArg (fun f => pullback.lift a b hab ≫ f) he
  simpa only [← Category.assoc, pullback.lift_fst, pullback.lift_snd] using hh

theorem finite_etale_quotient_iso (p : X ⟶ Y) (q : X ⟶ Z)
    [IsFinite p.left] [Etale p.left] [Surjective p.left]
    [IsFinite q.left] [Etale q.left] [Surjective q.left]
    (h : ∀ (T : Over S) [IsReduced T.left] (a b : T ⟶ X),
      a ≫ p = b ≫ p ↔ a ≫ q = b ≫ q) :
    ∃ e : Y ≅ Z, p ≫ e.hom = q := by
  obtain ⟨f, hf, _⟩ := finite_etale_factor_of_reduced_fibers p q (fun T _ a b => (h T a b).mp)
  obtain ⟨g, hg, _⟩ := finite_etale_factor_of_reduced_fibers q p (fun T _ a b => (h T a b).mpr)
  have hfg : f ≫ g = 𝟙 Y := by
    apply Over.OverMorphism.ext
    apply (cancel_epi p.left).mp
    have he : p ≫ f ≫ g = p ≫ 𝟙 Y := by rw [← Category.assoc, hf, hg, Category.comp_id]
    exact congrArg Over.Hom.left he
  have hgf : g ≫ f = 𝟙 Z := by
    apply Over.OverMorphism.ext
    apply (cancel_epi q.left).mp
    have he : q ≫ g ≫ f = q ≫ 𝟙 Z := by rw [← Category.assoc, hg, hf, Category.comp_id]
    exact congrArg Over.Hom.left he
  exact ⟨⟨f, g, hfg, hgf⟩, hf⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleQuotientComparison
