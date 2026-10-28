import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Chart Section Pullback -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartSectionPullback

noncomputable section

/-! Pulling a standard projective chart section back to its affine
chart gives the canonical global section of the chart ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
variable {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) (hd : 0 < d)

theorem projectiveChart_pullback_section
    (h : ⊤ ≤ Proj.awayι 𝒜 s hs hd ⁻¹ᵁ Proj.basicOpen 𝒜 s) :
    Proj.awayToSection 𝒜 s ≫ (Proj.awayι 𝒜 s hs hd).appLE (Proj.basicOpen 𝒜 s) ⊤ h =
      (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 s))).inv := by
  let U := Proj.basicOpen 𝒜 s
  let e := Proj.basicOpenIsoSpec 𝒜 s hs hd
  have hU : U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := rfl
  have he : e.hom.appTop = (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection 𝒜 s ≫ U.topIso.inv :=
    Proj.basicOpenToSpec_app_top 𝒜 s
  have hi : (Proj.awayι 𝒜 s hs hd).appLE U ⊤ h = U.topIso.inv ≫ e.inv.appTop := by
    rw [← hU]
    exact (Scheme.Hom.appLE_comp_appLE e.inv U.ι U ⊤ ⊤ U.ι_preimage_self.ge le_rfl).symm
  rw [← Iso.inv_comp_eq] at he
  calc
    Proj.awayToSection 𝒜 s ≫ (Proj.awayι 𝒜 s hs hd).appLE U ⊤ h =
        (Scheme.ΓSpecIso _).inv ≫ e.hom.appTop ≫ e.inv.appTop := by
          rw [hi, ← Category.assoc, ← he, Category.assoc]
    _ = (Scheme.ΓSpecIso _).inv := by
      rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop, Category.comp_id]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartSectionPullback
