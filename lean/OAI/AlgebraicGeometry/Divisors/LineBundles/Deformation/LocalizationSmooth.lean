import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.BaseScalarTower
import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.LocalizationLocus

/-! # Localization Smooth -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.LocalizationSmooth.BundleCycles

noncomputable section

/-! Smoothness of the deformation at a prime can be detected after
localizing the ambient coefficient ring at its actual contraction. -/

theorem deformationLocalization_formallySmooth_congr
    (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (I : Ideal R)
    {p q : Ideal R} [p.IsPrime] [q.IsPrime] (hpq : p = q)
    (h : Algebra.FormallySmooth A
      (Iff.BundleCycles.deformationAlgebra (I.map (algebraMap R (Localization.AtPrime p))))) :
    Algebra.FormallySmooth A
      (Iff.BundleCycles.deformationAlgebra (I.map (algebraMap R (Localization.AtPrime q)))) := by
  subst q
  exact h

theorem deformation_isSmoothAt_of_coefficientLocalization
    (A R : Type) [CommRing A] [CommRing R] [Algebra A R]
    (I : Ideal R) (q : PrimeSpectrum (Iff.BundleCycles.deformationAlgebra I))
    (h : Algebra.FormallySmooth A
      (Iff.BundleCycles.deformationAlgebra (I.map (algebraMap R
        (Localization.AtPrime (q.asIdeal.comap (algebraMap R (Iff.BundleCycles.deformationAlgebra I)))))))) :
    Algebra.IsSmoothAt A q.asIdeal := by
  let p := q.asIdeal.comap (algebraMap R (Iff.BundleCycles.deformationAlgebra I))
  let S := Localization.AtPrime p
  let D := Iff.BundleCycles.deformationAlgebra (I.map (algebraMap R S))
  let : Algebra (Iff.BundleCycles.deformationAlgebra I) D := (Deformation.Localization.BundleCycles.deformationBaseMap I S).toAlgebra
  let : IsScalarTower A (Iff.BundleCycles.deformationAlgebra I) D := BaseScalarTower.BundleCycles.deformationBaseMap_scalarTower A R S I
  let : IsLocalization (Deformation.Localization.BundleCycles.deformationDenominators I p.primeCompl) D :=
    Deformation.Localization.BundleCycles.deformationBaseMap_isLocalization I p.primeCompl S
  let : Algebra.FormallySmooth A D := h
  have hdisj : Disjoint (Deformation.Localization.BundleCycles.deformationDenominators I p.primeCompl : Set (Iff.BundleCycles.deformationAlgebra I))
      (q.asIdeal : Set (Iff.BundleCycles.deformationAlgebra I)) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨r, hr, rfl⟩ hz
    exact hr hz
  have hq : q ∈ Set.range (PrimeSpectrum.comap (algebraMap (Iff.BundleCycles.deformationAlgebra I) D)) := by
    rw [PrimeSpectrum.localization_comap_range D (Deformation.Localization.BundleCycles.deformationDenominators I p.primeCompl)]
    exact hdisj
  obtain ⟨q', hq'⟩ := hq
  have h' := Smooth.LocalizationLocus.BundleCycles.isSmoothAt_of_localization A (Iff.BundleCycles.deformationAlgebra I) D
    (Deformation.Localization.BundleCycles.deformationDenominators I p.primeCompl) q'
  exact hq' ▸ h'

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.LocalizationSmooth.BundleCycles
