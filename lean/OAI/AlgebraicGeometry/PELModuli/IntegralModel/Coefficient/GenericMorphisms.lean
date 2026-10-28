import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.CommonStage
import OAI.ArithmeticGeometry.Models.SpreadingOut.Diagram
import OAI.ArithmeticGeometry.Models.DiagramComposition

/-! # Generic Morphisms -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.GenericMorphisms.Coefficients

noncomputable section

/-! Generalization of the proved GenericMorphisms construction to a
general coefficient ring for smooth proper complex group-scheme families.

 Descent of finite sets of maps in fixed generic fibers, with one natural
comparison for all objects. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.NumberField

universe u v w

open OAI.ArithmeticGeometry.Models.SpreadingOut.Diagram.Construction

open OAI.ArithmeticGeometry.Models.DiagramComposition.Constructions.Foundations

structure CoefficientGenericComparisonData
    {R₀ K : Type u} [CommRing R₀] [Field K] [Algebra R₀ K] {s t : Finset K} (h : s ⊆ t) where
  iso : Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K h) ⋙
      Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K t) ≅
        Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s)
  component (M : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K s)) :
    (iso.app M).hom =
      (Over.isoMk (Morphisms.Coefficients.genericModelLift_cartesian
        (X := (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s)).obj M) M
        (pullback.fst M.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s)) (.of_hasPullback _ _) h).isoPullback.symm
        (Morphisms.Coefficients.genericModelLift_cartesian
          (X := (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s)).obj M) M
          (pullback.fst M.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s))
          (.of_hasPullback _ _) h).isoPullback_inv_snd).hom

theorem coefficientGenericComparisonData_exists
    {R₀ K : Type u} [CommRing R₀] [Field K] [Algebra R₀ K] {s t : Finset K} (h : s ⊆ t) :
    Nonempty (CoefficientGenericComparisonData (R₀ := R₀) h) := by
  refine ⟨{
    iso := ArithmeticGeometry.Models.DiagramComposition.Constructions.Foundations.baseChangeDiagramIso (𝟭 _) (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K h)
      (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K t) (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s) (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap_comp R₀ K h)
    component := fun M ↦ ?_
  }⟩
  rfl

def coefficientGenericComparison {R₀ K : Type u} [CommRing R₀] [Field K] [Algebra R₀ K] {s t : Finset K} (h : s ⊆ t) :
    Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K h) ⋙
      Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K t) ≅
        Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s) :=
  (coefficientGenericComparisonData_exists (R₀ := R₀) h).some.iso

def coefficientGenericComparisonAt {R₀ K : Type u} [CommRing R₀] [Field K] [Algebra R₀ K] {s t : Finset K}
    (h : s ⊆ t) (M : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K s)) :
    (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K t)).obj
      ((Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K h)).obj M) ≅
        (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s)).obj M :=
  (coefficientGenericComparison (R₀ := R₀) h).app M

theorem coefficientGenericComparison_hom
    {R₀ K : Type u} [CommRing R₀] [Field K] [Algebra R₀ K] {s t : Finset K} (h : s ⊆ t)
    (M : Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K s)) :
    ((coefficientGenericComparison (R₀ := R₀) h).app M).hom =
      (Over.isoMk (Morphisms.Coefficients.genericModelLift_cartesian
        (X := (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s)).obj M) M
        (pullback.fst M.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s)) (.of_hasPullback _ _) h).isoPullback.symm
        (Morphisms.Coefficients.genericModelLift_cartesian
          (X := (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s)).obj M) M
          (pullback.fst M.hom (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s))
          (.of_hasPullback _ _) h).isoPullback_inv_snd).hom :=
  (coefficientGenericComparisonData_exists (R₀ := R₀) h).some.component M

theorem finite_generic_morphisms_descend
    {R₀ K : Type u} [CommRing R₀] [Field K] [Algebra R₀ K] {s : Finset K} {ι : Type v} {α : Type w} [Finite α]
    (M : ι → Over (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase R₀ K s))
    (hM : ∀ i, ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (M i).hom)
    (src dst : α → ι)
    (a : ∀ j, (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s)).obj (M (src j)) ⟶
      (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s)).obj (M (dst j))) :
    ∃ (t : Finset K) (h : s ⊆ t)
      (b : ∀ j, (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K h)).obj (M (src j)) ⟶
        (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBaseMap R₀ K h)).obj (M (dst j))),
      ∀ j, (Over.pullback (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K t)).map (b j) ≫
        ((coefficientGenericComparison (R₀ := R₀) h).app (M (dst j))).hom =
        ((coefficientGenericComparison (R₀ := R₀) h).app (M (src j))).hom ≫ a j := by
  let g := ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K s
  obtain ⟨t, h, b, hb⟩ := CommonStage.Coefficients.finite_morphisms_descend src dst
    (fun i ↦ (Over.pullback g).obj (M i)) M hM
    (fun i ↦ pullback.fst (M i).hom g) (fun i ↦ .of_hasPullback _ _) a
  refine ⟨t, h, b, fun j ↦ ?_⟩
  rw [coefficientGenericComparison_hom, coefficientGenericComparison_hom]
  have H := ArithmeticGeometry.Models.SpreadingOut.Diagram.Construction.cartesian_generic_iso_compatibility (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap R₀ K t)
    _ _ (Morphisms.Coefficients.genericModelLift_cartesian (X := (Over.pullback g).obj (M (src j)))
      (M (src j)) (pullback.fst _ g) (.of_hasPullback _ _) h)
    (Morphisms.Coefficients.genericModelLift_cartesian (X := (Over.pullback g).obj (M (dst j)))
      (M (dst j)) (pullback.fst _ g) (.of_hasPullback _ _) h)
    (a j) (b j) (hb j)
  exact H

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Coefficient.GenericMorphisms.Coefficients
