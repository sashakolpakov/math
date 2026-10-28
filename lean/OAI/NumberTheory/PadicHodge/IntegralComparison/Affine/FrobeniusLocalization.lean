import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.FrobeniusRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.EtaleLocalization

/-! # Frobenius Localization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.FrobeniusLocalization

noncomputable section

/-!
# IntegralComparison: the original affine Frobenius module presheaf is localizing
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (k C σ : Type u) [Field k] [Fintype k] [CommRing C] [Algebra k C] [LinearOrder σ]
  [Algebra (MvPolynomial σ k) C] [IsScalarTower k (MvPolynomial σ k) C]
  [Algebra.FormallyEtale (MvPolynomial σ k) C]

include σ in
theorem principal_map (c : C) (n : ℕ) : IsLocalizedModule (Submonoid.powers c)
    (FrobeniusSections.map k C (PrimeSpectrum.basicOpen c) n).hom := by
  let U : (Spec (CommRingCat.of C)).Opens := PrimeSpectrum.basicOpen c
  let D : CommAlgCat.{u} k :=
    (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k (Crystalline.Presentation.affineScheme k C)).obj (op U)
  let : Algebra C D := AffineSection.Towers.coordinateAlgebra C U
  let : IsScalarTower k C D := AffineSection.Towers.tower k C U
  let : Algebra (MvPolynomial σ k) D := AffineSection.Coordinates.polynomialAlgebra k C σ U
  let : IsScalarTower k (MvPolynomial σ k) D := AffineSection.Coordinates.base_tower k C σ U
  let : IsScalarTower (MvPolynomial σ k) C D := AffineSection.Coordinates.coordinate_tower k C σ U
  let : Algebra.FormallyEtale (MvPolynomial σ k) D := AffineSection.Coordinates.principal_etale k C σ c
  let : IsLocalization.Away c D := CoordinateSections.principal_localization C c
  exact Frobenius.EtaleLocalization.isLocalizedModule k C D σ (Submonoid.powers c) n

include σ in
theorem restriction (c : C) (n : ℕ) : IsLocalizedModule (Submonoid.powers c)
    (FrobeniusSections.restrictionMap k C c n).hom :=
  FrobeniusRestriction.restriction k C c n (principal_map k C σ c n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.FrobeniusLocalization
