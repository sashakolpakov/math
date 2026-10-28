import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.FrameChanges
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.SectionLinearCoordinateAction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GeneratingSectionFrameChanges
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveTargetIso

/-! # Coordinate Transitivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.CoordinateTransitivity

noncomputable section

/-! Two complete generating families of isomorphic line bundles on the
same scheme define projective embeddings related by an actual invertible
coordinate change over the base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (L M : Line.Bundles.LineBundle X) {n : ℕ}
variable (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
variable (t : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M.sheaf))
variable (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
variable (ht : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (t i))
variable (hbs : Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination f.appTop.hom L.sheaf s))
variable (hbt : Function.Bijective (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination f.appTop.hom M.sheaf t))
variable (φ : L.sheaf ≅ M.sheaf)

theorem completeSectionFrameChange_transformed_section (j : Fin (n + 1)) :
    CoefficientTransformations.transformSectionFamily f.appTop.hom L.sheaf s
        (FrameChanges.completeSectionFrameChange f.appTop.hom s t hbs hbt φ).symm.toLinearMap j ≫ φ.hom = t j := by
  let e := FrameChanges.completeSectionFrameChange f.appTop.hom s t hbs hbt φ
  let Cs := Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination f.appTop.hom L.sheaf s
  let Ct := Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination f.appTop.hom M.sheaf t
  let vt := Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv f.appTop.hom M.sheaf
  let ψ := Coefficient.SectionBundleTransport.coefficientBundleSectionEquiv f.appTop.hom φ
  let a := e.symm (Finsupp.single j 1)
  have he : Ct (Finsupp.single j 1) = ψ (Cs a) :=
    (congrArg Ct (e.apply_symm_apply (Finsupp.single j 1))).symm.trans
      (FrameChanges.completeSectionFrameChange_commutes f.appTop.hom s t hbs hbt φ a)
  apply vt.injective
  exact (Coefficient.SectionBundleTransport.coefficientRingSectionAddEquiv_postcomp f.appTop.hom φ.hom _).trans
    ((congrArg ψ (CoefficientTransformations.coefficientSectionCombination_value f.appTop.hom L.sheaf s a)).trans
      (he.symm.trans (Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination_single f.appTop.hom M.sheaf t j)))

theorem completeSectionEmbeddings_coordinate_transitivity :
    SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs ≫
      (Relative.LinearCoordinateIsomorphism.relativeLinearCoordinateIso n S (FrameChanges.completeSectionFrameChange f.appTop.hom s t hbs hbt φ)).hom =
    SectionsProjectiveMorphism.sectionProjectiveMorphism f t ht := by
  let e := FrameChanges.completeSectionFrameChange f.appTop.hom s t hbs hbt φ
  let s' := CoefficientTransformations.transformSectionFamily f.appTop.hom L.sheaf s e.symm.toLinearMap
  have hs' : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s' i) :=
    GeneratingSectionFrameChanges.transformSectionFamily_covers f.appTop.hom L s hs e.symm.toLinearMap e.symm.surjective
  have hsφ := ProjectiveTargetIso.sections_compIso_covers φ s' hs'
  have hsections : (fun j => s' j ≫ φ.hom) = t := by
    funext j
    exact completeSectionFrameChange_transformed_section f L M s t hbs hbt φ j
  exact (Relative.SectionLinearCoordinateAction.sectionProjectiveMorphism_linearCoordinateIso f s hs e hs').trans
    ((ProjectiveTargetIso.sectionProjectiveMorphism_targetIso f φ s' hs' hsφ).trans
      (ProjectiveTargetIso.sectionProjectiveMorphism_congr f hsections hsφ ht))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.CoordinateTransitivity
