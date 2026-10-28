import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Flatness
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! # Map Over Base -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.MapOverBase

noncomputable section

/-!
Projective spectrum maps induced by graded maps that preserve coefficients
commute with their structure morphisms to the coefficient spectrum.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Flatness.GradedHilbert

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

theorem projectiveStructureMap_positiveAway {d : ℕ} (hd : 0 < d)
    {s : A} (hs : s ∈ 𝒜 d) :
    Proj.awayι 𝒜 s hs hd ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap 𝒜 =
      Spec.map (CommRingCat.ofHom (algebraMap R (HomogeneousLocalization.Away 𝒜 s))) := by
  rw [HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap, ← Category.assoc, Proj.awayι_toSpecZero,
    ← Spec.map_comp, HilbertScheme.Presentations.Homogeneous.LocalizationFlat.GradedHilbert.homogeneousLocalization_algebraMap]
  rfl

theorem homogeneousAwayMap_preserves_coefficients (f : 𝒜 →+*ᵍ ℬ)
    (hf : ∀ r : R, f (algebraMap R A r) = algebraMap R B r) (s : A) (r : R) :
    HomogeneousLocalization.Away.map f s
        (algebraMap R (HomogeneousLocalization.Away 𝒜 s) r) =
      algebraMap R (HomogeneousLocalization.Away ℬ (f s)) r := by
  rw [HilbertScheme.Presentations.Homogeneous.LocalizationFlat.GradedHilbert.homogeneousLocalization_algebraMap, HilbertScheme.Presentations.Homogeneous.LocalizationFlat.GradedHilbert.homogeneousLocalization_algebraMap]
  apply HomogeneousLocalization.val_injective
  change (HomogeneousLocalization.map f _
    (HomogeneousLocalization.mk ⟨0, algebraMap R (𝒜 0) r, 1, Submonoid.one_mem _⟩)).val = _
  rw [HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]
  change Localization.mk (f (algebraMap R A r)) (⟨f 1, _⟩ : Submonoid.powers (f s)) =
    Localization.mk (algebraMap R B r) 1
  simp only [hf, map_one]
  rfl

theorem projectiveMap_over_base (f : 𝒜 →+*ᵍ ℬ)
    (hi : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hf : ∀ r : R, f (algebraMap R A r) = algebraMap R B r) :
    Proj.map f hi ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap 𝒜 = HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap ℬ := by
  apply (Proj.mapAffineOpenCover f hi).openCover.hom_ext
  intro s
  change (d : ℕ+) × 𝒜 d at s
  rcases s with ⟨⟨d, hd⟩, s, hs⟩
  change s ∈ 𝒜 d at hs
  change Proj.awayι ℬ (f s) (f.map_mem hs) hd ≫
    (Proj.map f hi ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap 𝒜) =
      Proj.awayι ℬ (f s) (f.map_mem hs) hd ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap ℬ
  rw [← Category.assoc, Proj.awayι_comp_map f hi hd s hs, Category.assoc,
    projectiveStructureMap_positiveAway, projectiveStructureMap_positiveAway,
    ← Spec.map_comp]
  apply congrArg (fun h => Spec.map (CommRingCat.ofHom h))
  apply RingHom.ext
  exact homogeneousAwayMap_preserves_coefficients 𝒜 ℬ f hf s

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.MapOverBase
