import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.AbsoluteLinearCoordinateAction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.BaseMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveBaseChange

/-! # Section Linear Coordinate Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.SectionLinearCoordinateAction

noncomputable section

/-! Relative section-defined projective morphisms commute with actual
invertible changes of projective coordinates over an arbitrary base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X S : Scheme.{u}} {M : X.Modules} {n : ℕ} (f : X ⟶ S)
variable (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M))
variable (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
variable (e : (Fin (n + 1) →₀ Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) →₀ Γ(S, ⊤)))
variable (ht : ∀ x : X, ∃ i,
  x ∈ Ample.LineBundles.sectionNonvanishing (Section.CoefficientTransformations.transformSectionFamily f.appTop.hom M s e.symm.toLinearMap i))

theorem sectionProjectiveMorphism_linearCoordinateIso :
    SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs ≫ (LinearCoordinateIsomorphism.relativeLinearCoordinateIso n S e).hom =
      SectionsProjectiveMorphism.sectionProjectiveMorphism f (Section.CoefficientTransformations.transformSectionFamily f.appTop.hom M s e.symm.toLinearMap) ht := by
  let a := LinearCoordinateIsomorphism.relativeLinearCoordinateIso n S e
  let b := LinearCoordinateIsomorphism.affineLinearCoordinateIso n e
  have hp : a.hom.left ≫ RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection S n =
      RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection S n ≫ b.hom.left :=
    Pullback.Comparisons.overPullback_map_left_fst b.hom S.toSpecΓ
  apply Over.OverMorphism.ext
  apply (RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection_isPullback S n).hom_ext
  · change ((SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left ≫ a.hom.left) ≫
      RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection S n =
      (SectionsProjectiveMorphism.sectionProjectiveMorphism f (Section.CoefficientTransformations.transformSectionFamily f.appTop.hom M s e.symm.toLinearMap) ht).left ≫
        RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection S n
    rw [Category.assoc, hp, ← Category.assoc, Section.ProjectiveBaseChange.sectionProjectiveMorphism_coefficientProjection,
      Section.ProjectiveBaseChange.sectionProjectiveMorphism_coefficientProjection]
    exact Section.AbsoluteLinearCoordinateAction.sectionAbsoluteMorphism_linearCoordinateIso f s hs e ht
  · exact (SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs ≫ a.hom).w.trans
      (SectionsProjectiveMorphism.sectionProjectiveMorphism f (Section.CoefficientTransformations.transformSectionFamily f.appTop.hom M s e.symm.toLinearMap) ht).w.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.SectionLinearCoordinateAction
