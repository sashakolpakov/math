import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoordinateSectionRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Canonical.ProjectiveSectionData

/-! # Coordinate Section Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.CoordinateSectionRecovery

noncomputable section

/-! Relative homogeneous coordinates pull back to the specified section
family under its actual twisting isomorphism, over every base scheme. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def relativeProjectiveCoordinateSection (S : Scheme.{u}) (n : ℕ) (j : Fin (n + 1)) :
    Line.Bundles.structureModule (Projective.ProjectivePresentations.projectiveSpaceOver S n).left ⟶ (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).sheaf :=
  Ample.LineBundles.pullbackSection (RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection S n)
    (Affine.CoordinateSectionRecovery.affineProjectiveCoordinateSection Γ(S, ⊤) n j)

theorem relativeCoordinateSectionData_sections (S : Scheme.{u}) (n : ℕ) :
    (Canonical.ProjectiveSectionData.relativeCoordinateSectionData S n).sections = relativeProjectiveCoordinateSection S n := rfl

variable {X S : Scheme.{u}} {M : X.Modules} {n : ℕ} (f : X ⟶ S)
variable (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M))
variable (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))

theorem sectionProjectiveTwistingBundleIso_coordinate (j : Fin (n + 1)) :
    Ample.LineBundles.pullbackSection (SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left (relativeProjectiveCoordinateSection S n j) ≫
      (RelativeProjective.TwistingBundle.sectionProjectiveTwistingBundleIso f s hs).hom = s j := by
  let a := (SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left
  let b := RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection S n
  let q := Affine.CoordinateSectionRecovery.affineProjectiveCoordinateSection Γ(S, ⊤) n j
  let h : a ≫ b = SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs :=
    Section.ProjectiveBaseChange.sectionProjectiveMorphism_coefficientProjection f s hs
  let e := (Scheme.Modules.pullbackCongr h).app (Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle Γ(S, ⊤) n).sheaf
  let v := Section.AbsoluteTwistingBundle.sectionAbsoluteTwistingBundleIso f s hs
  change Ample.LineBundles.pullbackSection a (Ample.LineBundles.pullbackSection b q) ≫
    ((Scheme.Modules.pullbackComp a b).hom.app _ ≫ e.hom ≫ v.hom) = s j
  have h₁ := Global.SectionPullbackComposition.pullbackSection_composition a b q
  have h₂ := Global.SectionPullbackComposition.pullbackSection_equality h q
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ e.hom ≫ v.hom) h₁).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ v.hom) h₂).trans
          (Affine.CoordinateSectionRecovery.sectionAbsoluteTwistingBundleIso_coordinate f s hs j))))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.CoordinateSectionRecovery
