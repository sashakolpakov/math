import OAI.ArithmeticGeometry.Models.SpreadingOut.Diagram
import OAI.ArithmeticGeometry.Models.DiagramComposition

/-! # Generic Morphisms -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.GenericMorphisms.Construction

noncomputable section

/-! Descent of finite sets of maps in fixed generic fibers, with one natural
comparison for all objects. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u v w

open OAI.ArithmeticGeometry.Models.DiagramComposition.Constructions.Foundations

structure CoefficientGenericComparisonData
    {K : Type u} [Field K] {s t : Finset K} (h : s ⊆ t) where
  iso : Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h) ⋙
      Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t) ≅
        Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)
  component (M : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)) :
    (iso.app M).hom =
      (Over.isoMk (ModelMorphisms.Constructions.Foundations.genericModelLift_cartesian
        (X := (Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj M) M
        (pullback.fst M.hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)) (.of_hasPullback _ _) h).isoPullback.symm
        (ModelMorphisms.Constructions.Foundations.genericModelLift_cartesian
          (X := (Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj M) M
          (pullback.fst M.hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s))
          (.of_hasPullback _ _) h).isoPullback_inv_snd).hom

theorem coefficientGenericComparisonData_exists
    {K : Type u} [Field K] {s t : Finset K} (h : s ⊆ t) :
    Nonempty (CoefficientGenericComparisonData h) := by
  refine ⟨{
    iso := DiagramComposition.Constructions.Foundations.baseChangeDiagramIso (𝟭 _) (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)
      (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t) (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s) (CoefficientSystem.Constructions.Foundations.genericBaseMap_comp (𝓞 K) K h)
    component := fun M ↦ ?_
  }⟩
  rfl

def coefficientGenericComparison {K : Type u} [Field K] {s t : Finset K} (h : s ⊆ t) :
    Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h) ⋙
      Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t) ≅
        Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s) :=
  (coefficientGenericComparisonData_exists h).some.iso

def coefficientGenericComparisonAt {K : Type u} [Field K] {s t : Finset K}
    (h : s ⊆ t) (M : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)) :
    (Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t)).obj
      ((Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)).obj M) ≅
        (Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj M :=
  (coefficientGenericComparison h).app M

theorem coefficientGenericComparison_hom
    {K : Type u} [Field K] {s t : Finset K} (h : s ⊆ t)
    (M : Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s)) :
    ((coefficientGenericComparison h).app M).hom =
      (Over.isoMk (ModelMorphisms.Constructions.Foundations.genericModelLift_cartesian
        (X := (Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj M) M
        (pullback.fst M.hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)) (.of_hasPullback _ _) h).isoPullback.symm
        (ModelMorphisms.Constructions.Foundations.genericModelLift_cartesian
          (X := (Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj M) M
          (pullback.fst M.hom (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s))
          (.of_hasPullback _ _) h).isoPullback_inv_snd).hom :=
  (coefficientGenericComparisonData_exists h).some.component M

theorem finite_generic_morphisms_descend
    {K : Type u} [Field K] {s : Finset K} {ι : Type v} {α : Type w} [Finite α]
    (M : ι → Over (CoefficientSystem.Constructions.Foundations.coefficientBase (𝓞 K) K s))
    (hM : ∀ i, Scheme.Constructions.Foundations.FinitePresentationMorphism (M i).hom)
    (src dst : α → ι)
    (a : ∀ j, (Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj (M (src j)) ⟶
      (Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s)).obj (M (dst j))) :
    ∃ (t : Finset K) (h : s ⊆ t)
      (b : ∀ j, (Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)).obj (M (src j)) ⟶
        (Over.pullback (CoefficientSystem.Constructions.Foundations.coefficientBaseMap (𝓞 K) K h)).obj (M (dst j))),
      ∀ j, (Over.pullback (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t)).map (b j) ≫
        ((coefficientGenericComparison h).app (M (dst j))).hom =
        ((coefficientGenericComparison h).app (M (src j))).hom ≫ a j := by
  let g := CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K s
  obtain ⟨t, h, b, hb⟩ := CommonStage.Constructions.Foundations.finite_morphisms_descend src dst
    (fun i ↦ (Over.pullback g).obj (M i)) M hM
    (fun i ↦ pullback.fst (M i).hom g) (fun i ↦ .of_hasPullback _ _) a
  refine ⟨t, h, b, fun j ↦ ?_⟩
  rw [coefficientGenericComparison_hom, coefficientGenericComparison_hom]
  have H := Diagram.Construction.cartesian_generic_iso_compatibility (CoefficientSystem.Constructions.Foundations.genericBaseMap (𝓞 K) K t)
    _ _ (ModelMorphisms.Constructions.Foundations.genericModelLift_cartesian (X := (Over.pullback g).obj (M (src j)))
      (M (src j)) (pullback.fst _ g) (.of_hasPullback _ _) h)
    (ModelMorphisms.Constructions.Foundations.genericModelLift_cartesian (X := (Over.pullback g).obj (M (dst j)))
      (M (dst j)) (pullback.fst _ g) (.of_hasPullback _ _) h)
    (a j) (b j) (hb j)
  exact H

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.GenericMorphisms.Construction
