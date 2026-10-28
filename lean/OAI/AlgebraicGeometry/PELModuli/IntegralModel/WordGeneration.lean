import OAI.AlgebraicGeometry.PELModuli.IntegralModel.WordBaseChange

/-! # Word Generation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.WordGeneration.DifferenceWords

noncomputable section

/-! Generation transfers along the exact model comparison of the source
map and its group target. This identifies the actual finite word maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem surjective_baseChanged_word_of_comparison
    {S T : Scheme} (g : T ⟶ S) {X A : Over S} [GrpObj A]
    {Y B : Over T} [GrpObj B]
    (b : X ⟶ A) (a : Y ⟶ B)
    (eX : (Over.pullback g).obj X ≅ Y) (eA : (Over.pullback g).obj A ≅ B)
    [IsMonHom eA.hom]
    (hb : (Over.pullback g).map b ≫ eA.hom = eX.hom ≫ a)
    (n : ℕ) (hn : Surjective (Words.DifferenceWords.map a n).left) :
    Surjective ((Over.pullback g).map (Words.DifferenceWords.map b n)).left := by
  let eD := WordBaseChange.DifferenceWords.baseChangeDomain g X n ≪≫ WordBaseChange.DifferenceWords.domainIso eX n
  have he : (Over.pullback g).map (Words.DifferenceWords.map b n) ≫ eA.hom = eD.hom ≫ Words.DifferenceWords.map a n := by
    rw [WordBaseChange.DifferenceWords.baseChange_map, Category.assoc,
      WordBaseChange.DifferenceWords.map_naturality ((Over.pullback g).map b) a eX.hom eA.hom hb,
      ← WordBaseChange.DifferenceWords.domainIso_hom, ← Category.assoc]
    rfl
  have : IsIso eA.hom.left := ((Over.forget T).mapIso eA).isIso_hom
  have : IsIso eD.hom.left := ((Over.forget T).mapIso eD).isIso_hom
  have : Surjective (Words.DifferenceWords.map a n).left := hn
  apply (MorphismProperty.cancel_right_of_respectsIso @Surjective _ eA.hom.left).mp
  rw [← Over.comp_left, he]
  exact inferInstanceAs (Surjective (eD.hom.left ≫ (Words.DifferenceWords.map a n).left))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.WordGeneration.DifferenceWords
