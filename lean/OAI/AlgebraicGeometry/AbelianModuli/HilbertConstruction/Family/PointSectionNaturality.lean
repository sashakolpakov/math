import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.PointSectionEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismBaseChange

/-! # Point Section Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.PointSectionNaturality

noncomputable section

/-! The unit section associated to a family point commutes with actual parameter base change and the canonical family comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

theorem pullbackUnitComparison_fst {S T : Scheme.{u}} (f : T ⟶ S) :
    (Functor.LaxMonoidal.ε (Over.pullback f)).left ≫ pullback.fst (𝟙 S) f = f := by
  have h := pullback.condition (f := 𝟙 S) (g := f)
  simp only [Category.comp_id] at h
  rw [Over.ε_pullback_left, h, IsIso.inv_hom_id_assoc]

variable {S : Scheme.{u}} {U T : Over S} (f : U ⟶ T) (A : Over S) (p : T ⟶ A)

theorem familyPointSection_fst :
    (PointSectionEquivalence.familyPointSectionEquiv A T p).left ≫ pullback.fst A.hom T.hom = p.left :=
  pullback.lift_fst _ _ _

theorem familyPointSection_geometric_natural :
    (PointSectionEquivalence.familyPointSectionEquiv A U (f ≫ p)).left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap f A =
      f.left ≫ (PointSectionEquivalence.familyPointSectionEquiv A T p).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, Single.ParameterBaseChange.singleParameterBaseChangeMap_comp, familyPointSection_fst,
      Category.assoc, familyPointSection_fst]
    rfl
  · have hf : Single.ParameterBaseChange.singleParameterBaseChangeMap f A ≫ pullback.snd A.hom T.hom =
        pullback.snd A.hom U.hom ≫ f.left := Single.ParameterFunctoriality.singleParameterBaseChangeMap_over f A
    have hu : (PointSectionEquivalence.familyPointSectionEquiv A U (f ≫ p)).left ≫ pullback.snd A.hom U.hom = 𝟙 U.left :=
      (PointSectionEquivalence.familyPointSectionEquiv A U (f ≫ p)).w
    have ht : (PointSectionEquivalence.familyPointSectionEquiv A T p).left ≫ pullback.snd A.hom T.hom = 𝟙 T.left :=
      (PointSectionEquivalence.familyPointSectionEquiv A T p).w
    rw [Category.assoc, hf, ← Category.assoc, hu]
    exact (Category.id_comp f.left).trans
      ((Category.assoc f.left (PointSectionEquivalence.familyPointSectionEquiv A T p).left (pullback.snd A.hom T.hom)).trans
        ((congrArg (fun k => f.left ≫ k) ht).trans (Category.comp_id f.left))).symm

theorem familyPointSection_natural :
    PointSectionEquivalence.familyPointSectionEquiv A U (f ≫ p) ≫ (Single.ParameterBaseChange.singleParameterBaseChangeIso f A).hom =
      Functor.LaxMonoidal.ε (Over.pullback f.left) ≫
        (Over.pullback f.left).map (PointSectionEquivalence.familyPointSectionEquiv A T p) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change ((PointSectionEquivalence.familyPointSectionEquiv A U (f ≫ p)).left ≫ (Single.ParameterBaseChange.singleParameterBaseChangeIso f A).hom.left) ≫
      pullback.fst ((Over.pullback T.hom).obj A).hom f.left =
        ((Functor.LaxMonoidal.ε (Over.pullback f.left)).left ≫
          ((Over.pullback f.left).map (PointSectionEquivalence.familyPointSectionEquiv A T p)).left) ≫
            pullback.fst ((Over.pullback T.hom).obj A).hom f.left
    have hp : ((Over.pullback f.left).map (PointSectionEquivalence.familyPointSectionEquiv A T p)).left ≫
        pullback.fst ((Over.pullback T.hom).obj A).hom f.left =
      pullback.fst (𝟙 T.left) f.left ≫ (PointSectionEquivalence.familyPointSectionEquiv A T p).left :=
      pullback.lift_fst _ _ _
    rw [Category.assoc, Single.ParameterFunctoriality.singleParameterBaseChangeIso_hom_fst,
      Category.assoc, hp, ← Category.assoc, pullbackUnitComparison_fst]
    exact familyPointSection_geometric_natural f A p
  · exact (PointSectionEquivalence.familyPointSectionEquiv A U (f ≫ p) ≫ (Single.ParameterBaseChange.singleParameterBaseChangeIso f A).hom).w.trans
      (Functor.LaxMonoidal.ε (Over.pullback f.left) ≫
        (Over.pullback f.left).map (PointSectionEquivalence.familyPointSectionEquiv A T p)).w.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.PointSectionNaturality
