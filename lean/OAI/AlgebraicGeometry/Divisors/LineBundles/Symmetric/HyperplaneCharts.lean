import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.DegreeOneCover
import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricRegular
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartRegular
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AffineCompactification

/-! # Hyperplane Charts -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.HyperplaneCharts.BundleCycles

noncomputable section

/-! The infinity hyperplane is locally cut out by the actual regular
fraction of the distinguished coordinate in each degree-one chart. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousLocalization

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

def symmetricHyperplaneCoordinate (v : R × M) :
    Away (Grading.BundleCycles.symmetricGrading R (R × M)) (SymmetricAlgebra.ι R (R × M) v) :=
  Away.isLocalizationElem (DegreeOneCover.BundleCycles.symmetricGenerator_degree R (R × M) v) (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M)

theorem symmetricHyperplaneCoordinate_isRegular (v : R × M) :
    IsRegular (symmetricHyperplaneCoordinate R M v) := by
  exact Graded.ChartRegular.BundleCycles.gradedAway_mk_isRegular (Grading.BundleCycles.symmetricGrading R (R × M)) (DegreeOneCover.BundleCycles.symmetricGenerator_degree R (R × M) v)
    1 (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable R M ^ 1) _
    (by simpa only [pow_one] using Augmented.SymmetricRegular.BundleCycles.augmentedSymmetricVariable_isRegular R M)

theorem symmetricHyperplaneCoordinate_affineOpen (v : R × M) :
    (DegreeOneCover.BundleCycles.symmetricDegreeOneCover R (R × M)).f v ⁻¹ᵁ (AffineCompactification.BundleCycles.symmetricAffineCompactification R M).opensRange =
      PrimeSpectrum.basicOpen (symmetricHyperplaneCoordinate R M v) := by
  rw [AffineCompactification.BundleCycles.symmetricAffineCompactification_opensRange]
  exact Proj.awayι_preimage_basicOpen (𝒜 := Grading.BundleCycles.symmetricGrading R (R × M))
    (DegreeOneCover.BundleCycles.symmetricGenerator_degree R (R × M) v)
    (by decide : 0 < 1) (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) (by decide : 0 < 1)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.HyperplaneCharts.BundleCycles
