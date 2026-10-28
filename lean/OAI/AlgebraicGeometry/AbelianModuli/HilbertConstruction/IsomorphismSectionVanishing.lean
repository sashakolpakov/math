import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.SectionEquality

/-! # Isomorphism Section Vanishing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsomorphismSectionVanishing

noncomputable section

/-! Pullback through an isomorphism detects vanishing of actual
module-sheaf sections. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem pullbackSection_iso_eq_zero_iff {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    {M : Y.Modules} (s : Line.Bundles.structureModule Y ⟶ M) : Ample.LineBundles.pullbackSection f s = 0 ↔ s = 0 := by
  rw [Local.SectionEquality.pullbackSection_eq_zero_iff_image]
  have htop : f ''ᵁ (⊤ : X.Opens) = ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange]
    ext y
    exact ⟨fun _ => trivial, fun _ => Scheme.Hom.mem_opensRange.mpr (f.homeomorph.surjective y)⟩
  rw [htop]
  constructor
  · intro h
    apply (Global.Sections.moduleSectionHomEquiv M).injective
    exact h
  · rintro rfl
    rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsomorphismSectionVanishing
