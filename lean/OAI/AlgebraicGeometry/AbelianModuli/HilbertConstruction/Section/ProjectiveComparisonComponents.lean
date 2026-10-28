import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ComparisonTransport

/-! # Projective Comparison Components -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveComparisonComponents

noncomputable section

/-! The bundle comparison and its separately checked coordinate identities. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X S : Scheme.{u}} {M Q : X.Modules} {n : ℕ} (f : X ⟶ S)
variable (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ M))
variable (t : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ Q))
variable (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
variable (ht : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (t i))
variable (h : SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs = SectionsProjectiveMorphism.sectionProjectiveMorphism f t ht)

def sameProjectiveMapBundleIso : M ≅ Q :=
  ComparisonTransport.sectionComparisonIso (RelativeProjective.TwistingBundle.sectionProjectiveTwistingBundleIso f s hs)
    (RelativeProjective.TwistingBundle.sectionProjectiveTwistingBundleIso f t ht)
    ((Scheme.Modules.pullbackCongr (congrArg Over.Hom.left h)).app
      (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).sheaf)

theorem sameProjectiveMapBundleIso_hom :
    (sameProjectiveMapBundleIso f s t hs ht h).hom =
      ComparisonTransport.sectionComparisonMap (RelativeProjective.TwistingBundle.sectionProjectiveTwistingBundleIso f s hs)
        (RelativeProjective.TwistingBundle.sectionProjectiveTwistingBundleIso f t ht)
        ((Scheme.Modules.pullbackCongr (congrArg Over.Hom.left h)).app
          (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).sheaf) :=
  ComparisonTransport.sectionComparisonIso_hom _ _ _

theorem sectionProjectiveComparison_coordinate (i : Fin (n + 1)) :
    let q := Relative.CoordinateSectionRecovery.relativeProjectiveCoordinateSection S n i
    let a := Ample.LineBundles.pullbackSection (SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left q
    let es := RelativeProjective.TwistingBundle.sectionProjectiveTwistingBundleIso f s hs
    a ≫ es.hom = s i :=
  Relative.CoordinateSectionRecovery.sectionProjectiveTwistingBundleIso_coordinate f s hs i

theorem sectionProjectiveComparison_transport (i : Fin (n + 1)) :
    let q := Relative.CoordinateSectionRecovery.relativeProjectiveCoordinateSection S n i
    let a := Ample.LineBundles.pullbackSection (SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left q
    let b := Ample.LineBundles.pullbackSection (SectionsProjectiveMorphism.sectionProjectiveMorphism f t ht).left q
    let e := (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left h)).app
      (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).sheaf
    a ≫ e.hom = b :=
  ComparisonTransport.pullbackSection_equality_isoApp (congrArg Over.Hom.left h) (Relative.CoordinateSectionRecovery.relativeProjectiveCoordinateSection S n i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveComparisonComponents
