import OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.Smooth
import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.LocalizationLocus

/-! # Punctured Smooth -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.PuncturedSmooth.BundleCycles

noncomputable section

/-! Every point away from the parameter divisor is smooth over the
original base whenever the ambient coefficient algebra is formally smooth. -/

theorem deformation_isSmoothAt_punctured (A R : Type) [CommRing A] [CommRing R]
    [Algebra A R] [Algebra.FormallySmooth A R] (I : Ideal R)
    (q : PrimeSpectrum (Iff.BundleCycles.deformationAlgebra I))
    (hq : Iff.BundleCycles.deformationParameter I ∉ q.asIdeal) : Algebra.IsSmoothAt A q.asIdeal := by
  let : Algebra.FormallySmooth A (LaurentPolynomial R) := Laurent.Smooth.BundleCycles.laurent_formallySmooth A R
  have hqrange : q ∈ Set.range
      (PrimeSpectrum.comap (algebraMap (Iff.BundleCycles.deformationAlgebra I) (LaurentPolynomial R))) := by
    rw [PrimeSpectrum.localization_away_comap_range (LaurentPolynomial R) (Iff.BundleCycles.deformationParameter I)]
    exact hq
  obtain ⟨q', hq'⟩ := hqrange
  have h := Smooth.LocalizationLocus.BundleCycles.isSmoothAt_of_localization A (Iff.BundleCycles.deformationAlgebra I) (LaurentPolynomial R)
    (Submonoid.powers (Iff.BundleCycles.deformationParameter I)) q'
  exact hq' ▸ h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.PuncturedSmooth.BundleCycles
