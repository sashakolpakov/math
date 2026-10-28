import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartSectionPullback

/-! # Projective Chart Sections -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ProjectiveChartSections

noncomputable section

/-! Evaluating projective chart sections along an actual affine chart
map agrees with the defining map of chart rings. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {R A C : Type u} [CommRing R] [CommRing A] [Algebra R A] [CommRing C]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
variable {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) (hd : 0 < d)

theorem affineProjectiveChart_pullback_section
    (φ : HomogeneousLocalization.Away 𝒜 s →+* C)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ Proj.awayι 𝒜 s hs hd) ⁻¹ᵁ Proj.basicOpen 𝒜 s) :
    Proj.awayToSection 𝒜 s ≫
        (Spec.map (CommRingCat.ofHom φ) ≫ Proj.awayι 𝒜 s hs hd).appLE (Proj.basicOpen 𝒜 s) ⊤ h =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).inv := by
  have hj : ⊤ ≤ Proj.awayι 𝒜 s hs hd ⁻¹ᵁ Proj.basicOpen 𝒜 s := by
    rw [← Proj.opensRange_awayι 𝒜 s hs hd, Scheme.Hom.preimage_opensRange]
  have hc := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom φ))
    (Proj.awayι 𝒜 s hs hd) (Proj.basicOpen 𝒜 s) ⊤ ⊤ hj le_rfl
  rw [← hc, ← Category.assoc, Projective.ChartSectionPullback.projectiveChart_pullback_section 𝒜 hs hd hj]
  exact (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ProjectiveChartSections
