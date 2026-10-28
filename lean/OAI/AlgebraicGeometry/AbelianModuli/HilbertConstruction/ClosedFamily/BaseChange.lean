import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.Families

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Base change of flat finitely presented closed families via pullback of their ideal sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S T : Scheme.{u}} (P : Over S) (I : P.left.IdealSheafData) (f : T ⟶ S)

/-- The morphism from the pulled-back closed subscheme to the original one. -/
def ClosedFamily.BaseChange.closedFamilyBaseChangeMap :
    (I.comap (pullback.fst P.hom f)).subscheme ⟶ I.subscheme :=
  (I.comapIso (pullback.fst P.hom f)).hom ≫ pullback.snd (pullback.fst P.hom f) I.subschemeι

/-- Pulling back the ideal sheaf gives the actual base-change square of family schemes. -/
theorem ClosedFamily.BaseChange.closedFamilyBaseChange_isPullback :
    IsPullback (ClosedFamily.BaseChange.closedFamilyBaseChangeMap P I f)
      ((I.comap (pullback.fst P.hom f)).subschemeι ≫ pullback.snd P.hom f)
      (I.subschemeι ≫ P.hom) f := by
  let p := pullback.fst P.hom f
  have hs : IsPullback (I.comap p).subschemeι (ClosedFamily.BaseChange.closedFamilyBaseChangeMap P I f) p I.subschemeι := by
    apply isPullback_of_isClosedImmersion
    · calc
        (I.comap p).subschemeι ≫ p = ((I.comapIso p).hom ≫ pullback.fst p I.subschemeι) ≫ p :=
          congrArg (fun a => a ≫ p) (I.comapIso_hom_fst p).symm
        _ = ClosedFamily.BaseChange.closedFamilyBaseChangeMap P I f ≫ I.subschemeι := by
          rw [Category.assoc, pullback.condition, ← Category.assoc]
          rfl
    · rw [I.ker_subschemeι, (I.comap p).ker_subschemeι]
  exact hs.flip.paste_vert (IsPullback.of_hasPullback P.hom f)

variable {P}

/-- Base change preserves flatness and local finite presentation of the closed family. -/
def Closed.Families.FlatClosedFamily.baseChange (F : Closed.Families.FlatClosedFamily P) (f : T ⟶ S) :
    Closed.Families.FlatClosedFamily ((Over.pullback f).obj P) where
  ideal := F.ideal.comap (pullback.fst P.hom f)
  flat := MorphismProperty.of_isPullback (P := @Flat)
    (ClosedFamily.BaseChange.closedFamilyBaseChange_isPullback P F.ideal f) F.flat
  locallyFinitePresentation := MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
    (ClosedFamily.BaseChange.closedFamilyBaseChange_isPullback P F.ideal f) F.locallyFinitePresentation

/-- The family scheme of the pulled-back ideal is canonically isomorphic over
the new base to the ordinary pullback of the original family. -/
def Closed.Families.FlatClosedFamily.baseChangeIso (F : Closed.Families.FlatClosedFamily P) (f : T ⟶ S) :
    (F.baseChange f).scheme ≅ (Over.pullback f).obj F.scheme :=
  Over.isoMk (ClosedFamily.BaseChange.closedFamilyBaseChange_isPullback P F.ideal f).isoPullback
    (ClosedFamily.BaseChange.closedFamilyBaseChange_isPullback P F.ideal f).isoPullback_hom_snd

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
