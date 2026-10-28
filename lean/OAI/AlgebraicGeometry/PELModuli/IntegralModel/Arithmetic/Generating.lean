import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PointedDiagramTransport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.WordGeneration
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.CoefficientModels

/-! # Generating -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Generating

noncomputable section

/-! Geometry retained when an arithmetic family fiber is rewritten with
the native scalar extension of its fixed source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

def affineProjectiveBaseChangeAlong {R K : Type} [CommRing R] [CommRing K]
    (p : Spec (.of K) ⟶ Spec (.of R)) (m : ℕ) :
    (Over.pullback p).obj (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R m) ≅ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace K m :=
  Group.BaseChangeComparisons.GroupBaseChange.congrIso (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R m) p
      (Spec.map (Spec.preimage p)) (Spec.map_preimage p).symm ≪≫
    (Projective.CoefficientModels.Coefficients.affineProjectiveBaseChangeIso (Spec.preimage p).hom m).symm

section Pointed

variable {C D : Type*} [Category C] [Category D]
  [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]

theorem pointed_map_after_source_iso (F : C ⥤ D) [F.Monoidal]
    {X Y : C} [GrpObj Y] {U : D}
    (x : 𝟙_ C ⟶ X) (z : 𝟙_ D ⟶ U) (e : F.obj X ≅ U) (a : X ⟶ Y)
    (hx : Section.Comparisons.mappedSection F x ≫ e.hom = z) (ha : x ≫ a = 1) :
    z ≫ (e.inv ≫ F.map a) = 1 := by
  rw [← hx, Category.assoc, Iso.hom_inv_id_assoc, Section.Comparisons.mappedSection_map F, ha]
  exact Section.Comparisons.mappedSection_one F Y

end Pointed

namespace DifferenceWords

theorem surjective_word_of_comparison {S : Scheme} {X A Y B : Over S}
    [GrpObj A] [GrpObj B] (b : X ⟶ A) (a : Y ⟶ B)
    (eX : X ≅ Y) (eA : A ≅ B) [IsMonHom eA.hom]
    (hb : b ≫ eA.hom = eX.hom ≫ a) (n : ℕ) (hn : Surjective (Words.DifferenceWords.map a n).left) :
    Surjective (Words.DifferenceWords.map b n).left := by
  let eD := WordBaseChange.DifferenceWords.domainIso eX n
  have he : Words.DifferenceWords.map b n ≫ eA.hom = eD.hom ≫ Words.DifferenceWords.map a n := by
    rw [WordBaseChange.DifferenceWords.domainIso_hom]
    exact WordBaseChange.DifferenceWords.map_naturality b a eX.hom eA.hom hb n
  have : IsIso eA.hom.left := ((Over.forget S).mapIso eA).isIso_hom
  have : IsIso eD.hom.left := ((Over.forget S).mapIso eD).isIso_hom
  have : Surjective (Words.DifferenceWords.map a n).left := hn
  apply (MorphismProperty.cancel_right_of_respectsIso @Surjective _ eA.hom.left).mp
  rw [← Over.comp_left, he]
  exact inferInstanceAs (Surjective (eD.hom.left ≫ (Words.DifferenceWords.map a n).left))

theorem surjective_word_of_baseChange {S T : Scheme} (u : T ⟶ S)
    {X A : Over S} [GrpObj A] (a : X ⟶ A) (n : ℕ)
    (h : Surjective ((Over.pullback u).map (Words.DifferenceWords.map a n)).left) :
    Surjective (Words.DifferenceWords.map ((Over.pullback u).map a) n).left := by
  have hc : Surjective ((WordBaseChange.DifferenceWords.baseChangeDomain u X n).hom.left ≫
      (Words.DifferenceWords.map ((Over.pullback u).map a) n).left) := by
    rw [← Over.comp_left, ← WordBaseChange.DifferenceWords.baseChange_map]
    exact h
  exact ⟨Function.Surjective.of_comp (g := (WordBaseChange.DifferenceWords.baseChangeDomain u X n).hom.left) hc.surj⟩

end DifferenceWords

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Generating
