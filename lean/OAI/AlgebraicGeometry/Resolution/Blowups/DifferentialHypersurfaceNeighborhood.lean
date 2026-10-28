import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialHypersurface
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.Derivation

/-! # Differential Hypersurface Neighborhood -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialHypersurfaceNeighborhood.Construction

noncomputable section

/-! Actual smooth hypersurface neighborhoods obtained by inverting a nonzero derivative. -/

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- The ambient open set where the selected derivative is invertible. -/
abbrev derivationNeighborhood (D : Derivation k A A) (z : A) := Localization.Away (D z)

/-- The actual hypersurface quotient on the open derivative neighborhood. -/
abbrev differentialHypersurfaceNeighborhood (D : Derivation k A A) (z : A) :=
  derivationNeighborhood D z ⧸ Ideal.span {algebraMap A (derivationNeighborhood D z) z}

/-- The hypersurface is smooth over the original base on the open set
where the selected relative derivative is invertible. -/
theorem differentialHypersurfaceNeighborhood_smooth [Algebra.Smooth k A]
    (D : Derivation k A A) (z : A) :
    Algebra.Smooth k (differentialHypersurfaceNeighborhood D z) := by
  let B := derivationNeighborhood D z
  let : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (D z))
  let : Algebra.Smooth A B := Algebra.Smooth.of_isLocalization_Away (D z)
  let : Algebra.Smooth k B := Algebra.Smooth.comp k A B
  apply Blowups.Smooth.DifferentialHypersurface.Construction.smooth_quotient_of_unit_derivative (Etale.Derivation.Construction.extendEtaleRingDerivation (S := B) D)
    (algebraMap A B z)
  rw [Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap]
  exact IsLocalization.Away.algebraMap_isUnit (D z)

variable {F : Type*} [Field F]

/-- A field-valued point with a nonzero derivative lifts to the actual
hypersurface neighborhood. -/
def differentialHypersurfaceNeighborhoodPoint (D : Derivation k A A) (z : A)
    (φ : A →+* F) (hz : φ z = 0) (hDz : φ (D z) ≠ 0) :
    differentialHypersurfaceNeighborhood D z →+* F :=
  Ideal.Quotient.lift _ (IsLocalization.Away.lift (g := φ) (D z) (isUnit_iff_ne_zero.mpr hDz)) (by
    change Ideal.span {algebraMap A (derivationNeighborhood D z) z} ≤
      RingHom.ker (IsLocalization.Away.lift (g := φ) (D z) (isUnit_iff_ne_zero.mpr hDz))
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change IsLocalization.Away.lift (g := φ) (D z) (isUnit_iff_ne_zero.mpr hDz)
      (algebraMap A (derivationNeighborhood D z) z) = 0
    rw [IsLocalization.Away.lift_eq, hz])

/-- The lifted point has the prescribed values on the original affine algebra. -/
theorem differentialHypersurfaceNeighborhoodPoint_algebraMap (D : Derivation k A A) (z : A)
    (φ : A →+* F) (hz : φ z = 0) (hDz : φ (D z) ≠ 0) (a : A) :
    differentialHypersurfaceNeighborhoodPoint D z φ hz hDz
      (algebraMap A (differentialHypersurfaceNeighborhood D z) a) = φ a := by
  change differentialHypersurfaceNeighborhoodPoint D z φ hz hDz
    (Ideal.Quotient.mk _ (algebraMap A (derivationNeighborhood D z) a)) = φ a
  rw [differentialHypersurfaceNeighborhoodPoint, Ideal.Quotient.lift_mk,
    IsLocalization.Away.lift_eq]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialHypersurfaceNeighborhood.Construction
