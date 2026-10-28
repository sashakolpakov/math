import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveComparisonComponents

/-! # Projective Morphism Bundle Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveMorphismBundleComparison

noncomputable section

/-! Assemble the cached coordinate identities into the bundle comparison theorem. -/
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

include f s t hs ht h in
abbrev sameProjectiveMapBundleIso_section (i : Fin (n + 1)) := by
  exact ComparisonTransport.sectionIsoComparison
    (Ample.LineBundles.pullbackSection (SectionsProjectiveMorphism.sectionProjectiveMorphism f s hs).left
      (Relative.CoordinateSectionRecovery.relativeProjectiveCoordinateSection S n i))
    (Ample.LineBundles.pullbackSection (SectionsProjectiveMorphism.sectionProjectiveMorphism f t ht).left
      (Relative.CoordinateSectionRecovery.relativeProjectiveCoordinateSection S n i)) (s i) (t i)
    (RelativeProjective.TwistingBundle.sectionProjectiveTwistingBundleIso f s hs)
    (RelativeProjective.TwistingBundle.sectionProjectiveTwistingBundleIso f t ht)
    ((Scheme.Modules.pullbackCongr (congrArg Over.Hom.left h)).app
      (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).sheaf)
    (ProjectiveComparisonComponents.sectionProjectiveComparison_coordinate f s hs i)
    (ProjectiveComparisonComponents.sectionProjectiveComparison_coordinate f t ht i)
    (ProjectiveComparisonComponents.sectionProjectiveComparison_transport f s t hs ht h i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveMorphismBundleComparison
