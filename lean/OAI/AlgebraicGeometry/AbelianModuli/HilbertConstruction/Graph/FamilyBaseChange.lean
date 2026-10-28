import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MorphismGraphFamilies

/-! # Family Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Base change of ideal-defined embeddings and the canonical comparison of morphism graphs. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

variable {S T : Scheme.{u}} {A B : Over S}

theorem Graph.FamilyBaseChange.overPullback_map_isPullback_flip (f : T ⟶ S) (p : A ⟶ B) :
    IsPullback ((Over.pullback f).map p).left (pullback.fst A.hom f)
      (pullback.fst B.hom f) p.left := by
  have hf : ((Over.pullback f).map p).left ≫ pullback.fst B.hom f =
      pullback.fst A.hom f ≫ p.left := pullback.lift_fst _ _ _
  have hs : ((Over.pullback f).map p).left ≫ pullback.snd B.hom f =
      pullback.snd A.hom f := pullback.lift_snd _ _ _
  apply IsPullback.of_right (t := (IsPullback.of_hasPullback B.hom f).flip) _ hf
  rw [hs, p.w]
  exact (IsPullback.of_hasPullback A.hom f).flip

theorem Graph.FamilyBaseChange.closedImmersion_ker_baseChange {X X' Y Y' : Scheme.{u}}
    {i : X ⟶ Y} {i' : X' ⟶ Y'} {a : X' ⟶ X} {b : Y' ⟶ Y}
    [IsClosedImmersion i] (H : IsPullback i' a b i) : i'.ker = i.ker.comap b :=
  (congrArg Scheme.Hom.ker H.isoPullback_hom_fst).symm.trans
    ((Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom _).trans
      (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i b))

theorem Closed.Families.FlatClosedFamily.ofEmbedding_baseChange (f : T ⟶ S) (i : A ⟶ B)
    [IsClosedImmersion i.left] [Flat A.hom] [LocallyOfFinitePresentation A.hom] :
    (Closed.Families.FlatClosedFamily.ofEmbedding i).baseChange f =
      @Closed.Families.FlatClosedFamily.ofEmbedding T ((Over.pullback f).obj B) ((Over.pullback f).obj A)
        ((Over.pullback f).map i)
        (MorphismProperty.overPullbackMap f i (inferInstance : IsClosedImmersion i.left))
        (inferInstanceAs (Flat (pullback.snd A.hom f)))
        (inferInstanceAs (LocallyOfFinitePresentation (pullback.snd A.hom f))) := by
  apply Closed.Families.FlatClosedFamily.ext
  exact (Graph.FamilyBaseChange.closedImmersion_ker_baseChange (Graph.FamilyBaseChange.overPullback_map_isPullback_flip f i)).symm

theorem Graph.FamilyBaseChange.familyGraph_pullback (f : T ⟶ S) (p : A ⟶ B) :
    MorphismGraphFamilies.familyGraph ((Over.pullback f).map p) ≫ (Functor.Monoidal.μIso (Over.pullback f) A B).hom =
      (Over.pullback f).map (MorphismGraphFamilies.familyGraph p) := by
  have h := Functor.Monoidal.lift_μ (F := Over.pullback f) (𝟙 A) p
  rw [CategoryTheory.Functor.map_id] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
