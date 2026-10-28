import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialHypersurfaceNeighborhood
import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialCoefficientOrder

/-! # Neighborhood Coefficient Order -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.NeighborhoodCoefficientOrder.Construction

noncomputable section

/-! Coefficient-order reduction on the actual smooth derivative neighborhood. -/

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- Normalize the chosen derivative on the ambient open set so that it
takes the hypersurface equation to one. -/
def normalizedNeighborhoodDerivation (D : Derivation k A A) (z : A) :
    Derivation k (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) :=
  letI : Algebra.FormallyEtale A (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (D z))
  let u := (IsLocalization.Away.algebraMap_isUnit (S := DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) (D z)).unit
  (u⁻¹ : (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z)ˣ) • Etale.Derivation.Construction.extendEtaleRingDerivation (S := DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) D

theorem normalizedNeighborhoodDerivation_equation (D : Derivation k A A) (z : A) :
    normalizedNeighborhoodDerivation D z (algebraMap A (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) z) = 1 := by
  let : Algebra.FormallyEtale A (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (D z))
  let u := (IsLocalization.Away.algebraMap_isUnit (S := DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) (D z)).unit
  change (u⁻¹ : (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z)ˣ) •
    Etale.Derivation.Construction.extendEtaleRingDerivation (S := DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) D
      (algebraMap A (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) z) = 1
  rw [Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, ← IsUnit.unit_spec
    (IsLocalization.Away.algebraMap_isUnit (S := DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) (D z))]
  exact Units.inv_mul u

variable [Algebra ℚ A]

/-- On the chosen neighborhood, order of any ideal is exactly the list
of differential coefficient-order conditions on the actual hypersurface. -/
theorem neighborhood_order_iff_coefficient_orders (D : Derivation k A A) (z : A)
    (J M : Ideal (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z))
    (hzM : algebraMap A (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) z ∈ M) (b : ℕ) :
    J ≤ M ^ b ↔ ∀ j < b,
      DifferentialCoefficientOrder.Construction.differentialCoefficientIdeal (normalizedNeighborhoodDerivation D z)
        (algebraMap A (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) z) J j ≤
      M.map (Ideal.Quotient.mk (Ideal.span {algebraMap A (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) z})) ^ (b - j) :=
  DifferentialCoefficientOrder.Construction.ideal_order_iff_differentialCoefficientIdeals (normalizedNeighborhoodDerivation D z)
    (algebraMap A (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) z)
    (normalizedNeighborhoodDerivation_equation D z) J M hzM b

end

end OAI.AlgebraicGeometry.Resolution.Blowups.NeighborhoodCoefficientOrder.Construction
