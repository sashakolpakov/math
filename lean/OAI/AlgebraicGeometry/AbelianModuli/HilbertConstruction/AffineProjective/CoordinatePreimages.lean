import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.CoordinateMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Preimages

/-! # Coordinate Preimages -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.CoordinatePreimages

noncomputable section

/-! Standard projective charts pull back to the prescribed principal affine opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : CommRingCat.{u}) (A : Type u) [CommRing A] [Algebra R A] {n : ℕ}

theorem affineProjectiveCoordinateMap_preimage (v : Fin (n + 1) → A)
    (i : Fin (n + 1)) (hi : v i = 1) (k : Fin (n + 1)) :
    CoordinateMaps.affineProjectiveCoordinateMap R A v i hi ⁻¹ᵁ
      Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X k) = PrimeSpectrum.basicOpen (v k) := by
  rw [CoordinateMaps.affineProjectiveCoordinateMap_global, ProjectiveChart.Preimages.projectiveChartMap_preimage]
  exact basicOpen_eq_of_affine (R := CommRingCat.of A) (v k)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.CoordinatePreimages
