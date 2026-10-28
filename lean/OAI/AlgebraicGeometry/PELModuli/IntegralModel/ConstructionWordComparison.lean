import OAI.AlgebraicGeometry.PELModuli.IntegralModel.WordBaseChange

/-! # Construction Word Comparison -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConstructionWordComparison.DifferenceWords

noncomputable section

/-! Surjectivity in the native Construction and arithmetic finite-word conventions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem word_surjective_of_e07 (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : X.toOver ⟶ A.toOver) (n : ℕ) (h : Surjective (Albanese.Construction.ImageWords.wordMap X A a n).left) :
    Surjective (Words.DifferenceWords.map a n).left := by
  let e := eqToIso (WordBaseChange.DifferenceWords.e07_domain X n)
  have : IsIso e.hom.left := ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e).isIso_hom
  have : Surjective (Albanese.Construction.ImageWords.wordMap X A a n).left := h
  rw [WordBaseChange.DifferenceWords.e07_map, Over.comp_left]
  exact inferInstanceAs (Surjective (e.hom.left ≫ (Albanese.Construction.ImageWords.wordMap X A a n).left))

theorem e07_surjective_of_word (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : X.toOver ⟶ A.toOver) (n : ℕ) (h : Surjective (Words.DifferenceWords.map a n).left) :
    Surjective (Albanese.Construction.ImageWords.wordMap X A a n).left := by
  have hc : Surjective ((eqToHom (WordBaseChange.DifferenceWords.e07_domain X n)).left ≫ (Albanese.Construction.ImageWords.wordMap X A a n).left) := by
    rw [← Over.comp_left, ← WordBaseChange.DifferenceWords.e07_map]
    exact h
  exact ⟨Function.Surjective.of_comp (g := (eqToHom (WordBaseChange.DifferenceWords.e07_domain X n)).left) hc.surj⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConstructionWordComparison.DifferenceWords
