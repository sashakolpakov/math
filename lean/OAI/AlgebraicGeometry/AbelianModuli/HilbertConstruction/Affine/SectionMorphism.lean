import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Preimages
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StandardProjectiveCharts
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Section Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SectionMorphism

noncomputable section

/-! Affineness and finiteness of the projective morphism constructed from affine nonvanishing opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S X : Scheme.{u}} {L : X.Modules} {n : ℕ}

/-- When its section nonvanishing opens are affine, the constructed projective morphism is affine. -/
theorem sectionAbsoluteMorphism_affine (f : X ⟶ S)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ha : ∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s i))) :
    IsAffineHom (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro x
  obtain ⟨i, hi⟩ := StandardProjectiveCharts.standardProjectiveCharts_cover Γ(S, ⊤) n x
  refine ⟨Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading Γ(S, ⊤) n) (MvPolynomial.X i), hi,
    StandardProjectiveCharts.standardProjectiveChart_isAffine Γ(S, ⊤) n i, ?_⟩
  rw [ProjectiveChart.Preimages.sectionAbsoluteMorphism_preimage]
  exact ha i

/-- Properness over an affine base makes the constructed absolute projective morphism proper. -/
theorem sectionAbsoluteMorphism_proper (f : X ⟶ S) [IsProper f] [IsAffine S]
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) :
    IsProper (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) := by
  have : IsProper (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs ≫ (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom) :=
    (SectionsProjectiveMorphism.sectionAbsoluteMorphism_over f s hs).symm ▸ inferInstance
  exact IsProper.of_comp _ (Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n).hom

/-- On a proper scheme over an affine base, an affine nonvanishing cover yields a finite
morphism to actual projective space. -/
theorem sectionAbsoluteMorphism_finite (f : X ⟶ S) [IsProper f] [IsAffine S]
    (s : Fin (n + 1) → (Line.Bundles.structureModule X ⟶ L))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (ha : ∀ i, IsAffineOpen (Ample.LineBundles.sectionNonvanishing (s i))) :
    IsFinite (SectionsProjectiveMorphism.sectionAbsoluteMorphism f s hs) :=
  IsFinite.iff_isProper_and_isAffineHom.mpr
    ⟨sectionAbsoluteMorphism_proper f s hs, sectionAbsoluteMorphism_affine f s hs ha⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SectionMorphism
