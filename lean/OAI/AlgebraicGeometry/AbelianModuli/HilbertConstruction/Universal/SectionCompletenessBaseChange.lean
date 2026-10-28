import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.CompletenessPullbackComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.SectionFiberCriterion

/-! # Section Completeness Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.SectionCompletenessBaseChange

noncomputable section

/-! Universal and geometric completeness of the specified section family
commute with arbitrary base change of the family and of the parameter map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S T Z : Scheme.{u}} (X : Over S) (M : X.left.Modules) (f : T ⟶ S)
variable {r : ℕ} (s : Fin r → (Line.Bundles.structureModule X.left ⟶ M)) (b : Z ⟶ T)

theorem universallyCompleteSectionFamily_baseChange_iff :
    SectionCompletenessOpen.UniversallyCompleteSectionFamily ((Over.pullback f).obj X).hom
      ((Scheme.Modules.pullback (pullback.fst X.hom f)).obj M)
      (fun i => Ample.LineBundles.pullbackSection (pullback.fst X.hom f) (s i)) b ↔
    SectionCompletenessOpen.UniversallyCompleteSectionFamily X.hom M s (b ≫ f) := by
  constructor
  · intro h Y _ a
    have hc := (Section.CompletenessPullbackComposition.sectionCompleteness_pullback_comp X M f (a ≫ b) s).mp (h Y a)
    change Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination
      (pullback.snd X.hom ((a ≫ b) ≫ f)).appTop.hom
      ((Scheme.Modules.pullback (pullback.fst X.hom ((a ≫ b) ≫ f))).obj M)
      (fun i => Ample.LineBundles.pullbackSection (pullback.fst X.hom ((a ≫ b) ≫ f)) (s i))) at hc
    rw [Category.assoc] at hc
    exact hc
  · intro h Y _ a
    apply (Section.CompletenessPullbackComposition.sectionCompleteness_pullback_comp X M f (a ≫ b) s).mpr
    change Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination
      (pullback.snd X.hom ((a ≫ b) ≫ f)).appTop.hom
      ((Scheme.Modules.pullback (pullback.fst X.hom ((a ≫ b) ≫ f))).obj M)
      (fun i => Ample.LineBundles.pullbackSection (pullback.fst X.hom ((a ≫ b) ≫ f)) (s i)))
    rw [Category.assoc]
    exact h Y a

theorem geometricallyCompleteSectionFamily_baseChange_iff :
    ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily ((Over.pullback f).obj X).hom
      ((Scheme.Modules.pullback (pullback.fst X.hom f)).obj M)
      (fun i => Ample.LineBundles.pullbackSection (pullback.fst X.hom f) (s i)) b ↔
    ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily X.hom M s (b ≫ f) := by
  constructor
  · intro h K _ a
    have hc := (Section.CompletenessPullbackComposition.sectionCompleteness_pullback_comp X M f (a ≫ b) s).mp (h K a)
    change Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination
      (pullback.snd X.hom ((a ≫ b) ≫ f)).appTop.hom
      ((Scheme.Modules.pullback (pullback.fst X.hom ((a ≫ b) ≫ f))).obj M)
      (fun i => Ample.LineBundles.pullbackSection (pullback.fst X.hom ((a ≫ b) ≫ f)) (s i))) at hc
    rw [Category.assoc] at hc
    exact hc
  · intro h K _ a
    apply (Section.CompletenessPullbackComposition.sectionCompleteness_pullback_comp X M f (a ≫ b) s).mpr
    change Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination
      (pullback.snd X.hom ((a ≫ b) ≫ f)).appTop.hom
      ((Scheme.Modules.pullback (pullback.fst X.hom ((a ≫ b) ≫ f))).obj M)
      (fun i => Ample.LineBundles.pullbackSection (pullback.fst X.hom ((a ≫ b) ≫ f)) (s i)))
    rw [Category.assoc]
    exact h K a

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.SectionCompletenessBaseChange
