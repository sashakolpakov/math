import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Flatness

/-! # Projective Charts -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveCharts.GradedHilbert

noncomputable section

/-! Flatness of actual projective families gives flatness on all homogeneous affine charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

theorem projectiveStructureMap_away_homogeneous {d : ℕ} (hd : 0 < d)
    {s : A} (hs : s ∈ 𝒜 d) :
    Proj.awayι 𝒜 s hs hd ≫ Projective.Flatness.GradedHilbert.projectiveStructureMap 𝒜 =
      Spec.map (CommRingCat.ofHom (algebraMap R (HomogeneousLocalization.Away 𝒜 s))) := by
  rw [Projective.Flatness.GradedHilbert.projectiveStructureMap, ← Category.assoc, Proj.awayι_toSpecZero,
    ← Spec.map_comp, Homogeneous.LocalizationFlat.GradedHilbert.homogeneousLocalization_algebraMap]
  rfl

theorem homogeneousChart_flat_of_projective_flat [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap 𝒜)]
    {d : ℕ} (hd : 0 < d) {s : A} (hs : s ∈ 𝒜 d) :
    Module.Flat R (HomogeneousLocalization.Away 𝒜 s) := by
  have h : Flat (Proj.awayι 𝒜 s hs hd ≫ Projective.Flatness.GradedHilbert.projectiveStructureMap 𝒜) :=
    Flat.comp _ _
  rw [projectiveStructureMap_away_homogeneous 𝒜 hd hs, Flat.SpecMap_iff] at h
  exact RingHom.flat_algebraMap_iff.mp h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveCharts.GradedHilbert
