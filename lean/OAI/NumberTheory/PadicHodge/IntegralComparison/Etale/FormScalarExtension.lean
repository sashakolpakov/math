import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryFormScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.BasisBaseChange
import Mathlib.RingTheory.Localization.BaseChange

/-! # Form Scalar Extension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.FormScalarExtension

noncomputable section

/-!
# IntegralComparison: ordinary forms on étale charts commute with scalar extension and localization
-/

universe u

variable (R C D σ : Type u) [CommRing R] [CommRing C] [CommRing D] [LinearOrder σ]
  [Algebra R C] [Algebra R D] [Algebra C D] [IsScalarTower R C D]
  [Algebra (MvPolynomial σ R) C] [Algebra (MvPolynomial σ R) D]
  [IsScalarTower R (MvPolynomial σ R) C] [IsScalarTower R (MvPolynomial σ R) D]
  [IsScalarTower (MvPolynomial σ R) C D]
  [Algebra.FormallyEtale (MvPolynomial σ R) C] [Algebra.FormallyEtale (MvPolynomial σ R) D]

omit [LinearOrder σ] [Algebra R C] [Algebra R D] [IsScalarTower R C D]
    [IsScalarTower R (MvPolynomial σ R) C] [IsScalarTower R (MvPolynomial σ R) D]
    [Algebra.FormallyEtale (MvPolynomial σ R) C] [Algebra.FormallyEtale (MvPolynomial σ R) D] in
theorem map_coordinate (i : σ) : algebraMap C D (CoordinateFormBasis.coordinate R C σ i) =
    CoordinateFormBasis.coordinate R D σ i :=
  (IsScalarTower.algebraMap_apply (MvPolynomial σ R) C D (MvPolynomial.X i)).symm

theorem map_basis (n : ℕ) (s : Set.powersetCard σ n) :
    OrdinaryFormScalars.Ordinary.map R C D n (CoordinateFormBasis.basis R C σ n s) =
      CoordinateFormBasis.basis R D σ n s := by
  rw [CoordinateFormBasis.basis_apply, OrdinaryFormScalars.Ordinary.map_symbol,
    CoordinateFormBasis.basis_apply, map_one]
  exact congrArg (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R D 1) (funext (fun i => map_coordinate R C D σ _))

include σ in
theorem isBaseChange (n : ℕ) : IsBaseChange D (OrdinaryFormScalars.Ordinary.map R C D n) :=
  BasisBaseChange.isBaseChange (OrdinaryFormScalars.Ordinary.map R C D n)
    (CoordinateFormBasis.basis R C σ n) (CoordinateFormBasis.basis R D σ n)
    (map_basis R C D σ n)

include σ in
theorem isLocalizedModule (S : Submonoid C) [IsLocalization S D] (n : ℕ) :
    IsLocalizedModule S (OrdinaryFormScalars.Ordinary.map R C D n) :=
  (isLocalizedModule_iff_isBaseChange S D _).mpr (isBaseChange R C D σ n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.FormScalarExtension
