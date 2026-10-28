import OAI.AlgebraicGeometry.Resolution.Blowups.AdaptedEtaleCoordinates
import OAI.AlgebraicGeometry.Resolution.Blowups.NeighborhoodCoefficientOrder

/-! # Adapted Derivative Neighborhood -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.AdaptedDerivativeNeighborhood.Construction

noncomputable section

/-! Straightening the actual derivative hypersurface while preserving its original equation. -/

open _root_.MvPolynomial

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] [Algebra.Smooth k A]

/-- At every point of the actual derivative neighborhood, an additional
localization gives étale coordinates with the original hypersurface equation
as a distinguished coordinate. No new hypersurface equation is substituted. -/
theorem derivativeNeighborhood_exists_adapted_coordinates (D : Derivation k A A) (z : A)
    (q : Ideal (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z)) [q.IsPrime] :
    ∃ f ∉ q, ∃ (n : ℕ) (φ : MvPolynomial (Fin n ⊕ Unit) k →+* Localization.Away f),
      φ.Etale ∧ (∀ r : k, φ (C r) = algebraMap k (Localization.Away f) r) ∧
      φ (X (Sum.inr ())) = algebraMap A (Localization.Away f) z := by
  let B := DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z
  let : Algebra.Smooth A B := Algebra.Smooth.of_isLocalization_Away (D z)
  let : Algebra.Smooth k B := Algebra.Smooth.comp k A B
  obtain ⟨f, hf, n, φ, hφ, hC, hX⟩ := AdaptedEtaleCoordinates.Construction.exists_adapted_etale_coordinates
    (NeighborhoodCoefficientOrder.Construction.normalizedNeighborhoodDerivation D z) (algebraMap A B z)
    (NeighborhoodCoefficientOrder.Construction.normalizedNeighborhoodDerivation_equation D z) q
  refine ⟨f, hf, n, φ, hφ, hC, ?_⟩
  exact hX.trans (IsScalarTower.algebraMap_apply A B (Localization.Away f) z).symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.AdaptedDerivativeNeighborhood.Construction
