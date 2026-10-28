import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.CoordinateMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.CoefficientNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.CoordinatesOver

/-! # Normalized Coefficient Square -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.NormalizedCoefficientSquare

noncomputable section

/-! Normalized affine projective coordinates commute with changes
of both the test ring and the ambient projective coefficient ring. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R A : Type u} [CommRing R] [CommRing A] {n : ℕ}

theorem affineProjectiveCoordinateMap_targetCoefficient (φ : R →+* A)
    (v : Fin (n + 1) → A) (i : Fin (n + 1)) (hi : v i = 1) :
    letI := φ.toAlgebra
    AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of A) A v i hi ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n =
      AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of R) A v i hi := by
  let := φ.toAlgebra
  rw [AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap_global, AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap_global,
    ProjectiveChart.CoefficientNaturality.projectiveChartMap_coefficientMap]
  rfl

theorem affineProjectiveCoordinateMap_coefficientSquare (φ : R →+* A)
    (v : Fin (n + 1) → R) (i : Fin (n + 1)) (hi : v i = 1) :
    Spec.map (CommRingCat.ofHom φ) ≫ AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of R) R v i hi =
      AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of A) A (fun j => φ (v j)) i
        ((congrArg φ hi).trans φ.map_one) ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n := by
  let := φ.toAlgebra
  rw [affineProjectiveCoordinateMap_targetCoefficient]
  let ψ : R →ₐ[R] A := { __ := φ, commutes' := fun _ => rfl }
  exact AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap_natural (.of R) R ψ v i hi

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.NormalizedCoefficientSquare
