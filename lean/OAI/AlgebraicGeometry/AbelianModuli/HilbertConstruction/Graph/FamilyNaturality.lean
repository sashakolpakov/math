import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.FamilyBaseChange

/-! # Family Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.FamilyNaturality

noncomputable section

/-! Graph families commute with arbitrary base change as actual ideal-defined closed families. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

variable {S T : Scheme.{u}} (f : T ⟶ S) (A B : Over S)

def overProductBaseChangeMap :
    ((Over.pullback f).obj A ⊗ (Over.pullback f).obj B).left ⟶ (A ⊗ B).left :=
  (Functor.Monoidal.μIso (Over.pullback f) A B).hom.left ≫ pullback.fst (A ⊗ B).hom f

theorem overProductBaseChange_isPullback :
    IsPullback (overProductBaseChangeMap f A B)
      ((Over.pullback f).obj A ⊗ (Over.pullback f).obj B).hom (A ⊗ B).hom f := by
  let e := Functor.Monoidal.μIso (Over.pullback f) A B
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget T).map e.hom))
  have H : IsPullback e.hom.left ((Over.pullback f).obj A ⊗ (Over.pullback f).obj B).hom
      (pullback.snd (A ⊗ B).hom f) (𝟙 T) :=
    IsPullback.of_horiz_isIso ⟨e.hom.w.trans (Category.comp_id _).symm⟩
  have H' := H.paste_horiz (IsPullback.of_hasPullback (A ⊗ B).hom f)
  simp only [Category.id_comp] at H'
  exact H'

variable {A B}

theorem familyGraph_baseChange_isPullback (p : A ⟶ B) :
    IsPullback (MorphismGraphFamilies.familyGraph ((Over.pullback f).map p)).left (pullback.fst A.hom f)
      (overProductBaseChangeMap f A B) (MorphismGraphFamilies.familyGraph p).left := by
  let e := Functor.Monoidal.μIso (Over.pullback f) A B
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget T).map e.hom))
  have H : IsPullback (MorphismGraphFamilies.familyGraph ((Over.pullback f).map p)).left
      (𝟙 ((Over.pullback f).obj A).left) e.hom.left ((Over.pullback f).map (MorphismGraphFamilies.familyGraph p)).left := by
    apply IsPullback.of_vert_isIso
    exact ⟨(congrArg Over.Hom.left (FamilyBaseChange.familyGraph_pullback f p)).trans (Category.id_comp _).symm⟩
  have H' := H.paste_vert (FamilyBaseChange.overPullback_map_isPullback_flip f (MorphismGraphFamilies.familyGraph p))
  simp only [Category.id_comp] at H'
  exact H'

theorem morphismGraphFamily_baseChange (p : A ⟶ B) [IsSeparated B.hom] [Flat A.hom]
    [LocallyOfFinitePresentation A.hom] :
    (MorphismGraphFamilies.morphismGraphFamily p).pullbackAlong (overProductBaseChangeMap f A B) f
      (overProductBaseChange_isPullback f A B) =
      @MorphismGraphFamilies.morphismGraphFamily T ((Over.pullback f).obj A) ((Over.pullback f).obj B)
        ((Over.pullback f).map p) (inferInstanceAs (IsSeparated (pullback.snd B.hom f)))
        (inferInstanceAs (Flat (pullback.snd A.hom f)))
        (inferInstanceAs (LocallyOfFinitePresentation (pullback.snd A.hom f))) := by
  apply Closed.Families.FlatClosedFamily.ext
  exact (FamilyBaseChange.closedImmersion_ker_baseChange (familyGraph_baseChange_isPullback f p)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.FamilyNaturality
