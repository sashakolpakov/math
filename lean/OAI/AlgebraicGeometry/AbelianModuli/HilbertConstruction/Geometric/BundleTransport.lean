import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.SectionFiberCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionBundleTransport

/-! # Bundle Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Geometric completeness of specified section maps is preserved by
an isomorphism of the actual line-bundle sheaves. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S X T : Scheme.{u}} (f : X ⟶ S) {M N : X.Modules}
variable {r : ℕ} (s : Fin r → (Line.Bundles.structureModule X ⟶ M)) (b : T ⟶ S)

theorem ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily.bundleIso
    (h : ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily f M s b) (e : M ≅ N) :
    ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily f N (fun i => s i ≫ e.hom) b := by
  intro K _ a
  let p := CategoryTheory.Limits.pullback.fst f (a ≫ b)
  let q := CategoryTheory.Limits.pullback.snd f (a ≫ b)
  let ep := (Scheme.Modules.pullback p).mapIso e
  have hs : (fun i => Ample.LineBundles.pullbackSection p (s i ≫ e.hom)) =
      fun i => Ample.LineBundles.pullbackSection p (s i) ≫ ep.hom := by
    funext i
    simp only [Ample.LineBundles.pullbackSection, Functor.map_comp, Category.assoc]
    rfl
  change Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination q.appTop.hom
    ((Scheme.Modules.pullback p).obj N) (fun i => Ample.LineBundles.pullbackSection p (s i ≫ e.hom)))
  rw [hs, Coefficient.SectionBundleTransport.coefficientSectionLinearCombination_postcomp]
  exact (Coefficient.SectionBundleTransport.coefficientBundleSectionEquiv q.appTop.hom ep).bijective.comp (h K a)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
