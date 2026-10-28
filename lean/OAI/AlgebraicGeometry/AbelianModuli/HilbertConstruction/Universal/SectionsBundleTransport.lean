import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.SectionCompletenessOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionBundleTransport

/-! # Sections Bundle Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal

noncomputable section

/-! Universal completeness of specified sections is invariant under
an isomorphism of the actual bundle sheaves. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S X T : Scheme.{u}} (f : X ⟶ S) {M N : X.Modules}
variable {r : ℕ} (s : Fin r → (Line.Bundles.structureModule X ⟶ M)) (b : T ⟶ S)

theorem SectionCompletenessOpen.UniversallyCompleteSectionFamily.bundleIso
    (h : SectionCompletenessOpen.UniversallyCompleteSectionFamily f M s b) (e : M ≅ N) :
    SectionCompletenessOpen.UniversallyCompleteSectionFamily f N (fun i => s i ≫ e.hom) b := by
  intro Y _ a
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
  exact (Coefficient.SectionBundleTransport.coefficientBundleSectionEquiv q.appTop.hom ep).bijective.comp (h Y a)

theorem SectionsBundleTransport.universallyCompleteSectionFamily_bundleIso_iff (e : M ≅ N) :
    SectionCompletenessOpen.UniversallyCompleteSectionFamily f N (fun i => s i ≫ e.hom) b ↔
      SectionCompletenessOpen.UniversallyCompleteSectionFamily f M s b := by
  constructor
  · intro h
    have h' := h.bundleIso f (fun i => s i ≫ e.hom) b e.symm
    simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using h'
  · intro h
    exact h.bundleIso f s b e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal
