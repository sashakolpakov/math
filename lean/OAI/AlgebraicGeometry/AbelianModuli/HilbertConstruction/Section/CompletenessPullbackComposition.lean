import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionIsomorphismCriteria
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.SectionPullbackComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Completeness Pullback Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.CompletenessPullbackComposition

noncomputable section

/-! Complete coefficient section families agree under the canonical
comparison between an iterated pullback and pullback along the composite.
The comparison preserves the actual specified section morphisms. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u v
variable {S T Y : Scheme.{u}} (X : Over S) (M : X.left.Modules) (f : T ⟶ S) (h : Y ⟶ T)

def iteratedSectionPullbackBundleIso :
    ((Scheme.Modules.pullback ((Over.pullbackComp h f).app X).hom.left).obj
      ((Scheme.Modules.pullback (pullback.fst ((Over.pullback f).obj X).hom h)).obj
        ((Scheme.Modules.pullback (pullback.fst X.hom f)).obj M))) ≅
      (Scheme.Modules.pullback (pullback.fst X.hom (h ≫ f))).obj M :=
  (Scheme.Modules.pullbackComp ((Over.pullbackComp h f).app X).hom.left
    (pullback.fst ((Over.pullback f).obj X).hom h)).app
      ((Scheme.Modules.pullback (pullback.fst X.hom f)).obj M) ≪≫
  (Scheme.Modules.pullbackComp
    (((Over.pullbackComp h f).app X).hom.left ≫ pullback.fst ((Over.pullback f).obj X).hom h)
    (pullback.fst X.hom f)).app M ≪≫
  (Scheme.Modules.pullbackCongr
    ((Category.assoc _ _ _).trans (Pullback.Comparisons.pullbackComp_hom_fst_fst X f h))).app M

theorem iteratedSectionPullbackBundleIso_section (s : Line.Bundles.structureModule X.left ⟶ M) :
    Ample.LineBundles.pullbackSection ((Over.pullbackComp h f).app X).hom.left
      (Ample.LineBundles.pullbackSection (pullback.fst ((Over.pullback f).obj X).hom h)
        (Ample.LineBundles.pullbackSection (pullback.fst X.hom f) s)) ≫
      (iteratedSectionPullbackBundleIso X M f h).hom =
        Ample.LineBundles.pullbackSection (pullback.fst X.hom (h ≫ f)) s := by
  change Ample.LineBundles.pullbackSection _ (Ample.LineBundles.pullbackSection _ (Ample.LineBundles.pullbackSection _ s)) ≫
    ((Scheme.Modules.pullbackComp _ _).hom.app _ ≫
      (Scheme.Modules.pullbackComp _ _).hom.app _ ≫
        (Scheme.Modules.pullbackCongr _).hom.app _) = _
  rw [← Category.assoc, ← Category.assoc, Global.SectionPullbackComposition.pullbackSection_composition,
    Global.SectionPullbackComposition.pullbackSection_composition, Global.SectionPullbackComposition.pullbackSection_equality]

theorem sectionCompleteness_pullback_comp {κ : Type v}
    (s : κ → (Line.Bundles.structureModule X.left ⟶ M)) :
    Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination
      (pullback.snd ((Over.pullback f).obj X).hom h).appTop.hom
      ((Scheme.Modules.pullback (pullback.fst ((Over.pullback f).obj X).hom h)).obj
        ((Scheme.Modules.pullback (pullback.fst X.hom f)).obj M))
      (fun i => Ample.LineBundles.pullbackSection (pullback.fst ((Over.pullback f).obj X).hom h)
        (Ample.LineBundles.pullbackSection (pullback.fst X.hom f) (s i)))) ↔
    Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination (pullback.snd X.hom (h ≫ f)).appTop.hom
      ((Scheme.Modules.pullback (pullback.fst X.hom (h ≫ f))).obj M)
      (fun i => Ample.LineBundles.pullbackSection (pullback.fst X.hom (h ≫ f)) (s i))) := by
  let e := (Over.pullbackComp h f).app X
  let N := (Scheme.Modules.pullback (pullback.fst ((Over.pullback f).obj X).hom h)).obj
    ((Scheme.Modules.pullback (pullback.fst X.hom f)).obj M)
  let t := fun i => Ample.LineBundles.pullbackSection (pullback.fst ((Over.pullback f).obj X).hom h)
    (Ample.LineBundles.pullbackSection (pullback.fst X.hom f) (s i))
  have he := (Coefficient.SectionIsomorphismCriteria.coefficientSections_bijective_sourceIso_iff e N t).symm.trans
    (Coefficient.SectionIsomorphismCriteria.coefficientSections_bijective_bundleIso_iff (pullback.snd X.hom (h ≫ f)).appTop.hom
      (iteratedSectionPullbackBundleIso X M f h) (fun i => Ample.LineBundles.pullbackSection e.hom.left (t i))).symm
  have hs : (fun i => Ample.LineBundles.pullbackSection e.hom.left (t i) ≫ (iteratedSectionPullbackBundleIso X M f h).hom) =
      fun i => Ample.LineBundles.pullbackSection (pullback.fst X.hom (h ≫ f)) (s i) := by
    funext i
    exact iteratedSectionPullbackBundleIso_section X M f h (s i)
  rw [hs] at he
  exact he

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.CompletenessPullbackComposition
