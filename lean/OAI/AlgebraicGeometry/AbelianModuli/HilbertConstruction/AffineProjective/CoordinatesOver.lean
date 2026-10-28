import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.CoordinateMaps

/-! # Coordinates Over -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.CoordinatesOver

noncomputable section

/-! Affine projective-coordinate maps commute with their specified coefficient base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : CommRingCat.{u}) (A : Type u) [CommRing A] [Algebra R A] {n : ℕ}

theorem affineProjectiveCoordinateMap_over (v : Fin (n + 1) → A)
    (i : Fin (n + 1)) (hi : v i = 1) :
    CoordinateMaps.affineProjectiveCoordinateMap R A v i hi ≫ (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [CoordinateMaps.affineProjectiveCoordinateMap_global, ProjectiveChart.Evaluation.projectiveChartMap_over,
    CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc]
  have h : (Spec (CommRingCat.of A)).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (S := Γ(Spec (CommRingCat.of A), ⊤))
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) = 𝟙 _ :=
    toSpecΓ_SpecMap_ΓSpecIso_inv (CommRingCat.of A)
  rw [h, Category.id_comp]

def affineProjectiveCoordinateOverMap (v : Fin (n + 1) → A)
    (i : Fin (n + 1)) (hi : v i = 1) :
    HilbertScheme.Presentations.Relative.AffinePoints.relativeAffineScheme R A ⟶ Projective.ProjectivePresentations.affineProjectiveSpace R n :=
  Over.homMk (CoordinateMaps.affineProjectiveCoordinateMap R A v i hi)
    (affineProjectiveCoordinateMap_over R A v i hi)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.CoordinatesOver
