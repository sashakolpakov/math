import OAI.AlgebraicGeometry.Resolution.Blowups.NeighborhoodCoefficientOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicBoundary
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.HypersurfaceDimension

/-! # Refined Normal Derivative -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.RefinedNormalDerivative.Construction

noncomputable section

/-! The normal derivative and dimension descent on the actual refined hypersurface open. -/

variable {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]

def refinedNormalDerivation (D : Derivation k A A) (z : A) (f : DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) :
    Derivation k (Localization.Away f) (Localization.Away f) :=
  Etale.Derivation.Construction.extendEtaleRingDerivation (S := Localization.Away f) (NeighborhoodCoefficientOrder.Construction.normalizedNeighborhoodDerivation D z)

theorem refinedNormalDerivation_equation (D : Derivation k A A) (z : A)
    (f : DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) :
    refinedNormalDerivation D z f (algebraMap A (Localization.Away f) z) = 1 := by
  rw [IsScalarTower.algebraMap_apply A (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) (Localization.Away f)]
  change Etale.Derivation.Construction.extendEtaleRingDerivation (S := Localization.Away f) (NeighborhoodCoefficientOrder.Construction.normalizedNeighborhoodDerivation D z)
    (algebraMap (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) (Localization.Away f)
      (algebraMap A (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) z)) = 1
  rw [Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, NeighborhoodCoefficientOrder.Construction.normalizedNeighborhoodDerivation_equation, map_one]

theorem normalizedNeighborhoodDerivation_relative_logarithmic
    (w : ι → A) (D : Derivation k A A) (hD : D ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w) (z : A) :
    NeighborhoodCoefficientOrder.Construction.normalizedNeighborhoodDerivation D z ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k
      (fun j => algebraMap A (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) (w j)) := by
  let V := DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z
  let : Algebra.FormallyEtale A V := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (D z))
  let u := (IsLocalization.Away.algebraMap_isUnit (S := V) (D z)).unit
  change (↑(u⁻¹) : V) • Etale.Derivation.Construction.extendEtaleRingDerivation (S := V) D ∈ _
  exact (Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k _).smul_mem _
    (Relative.LogarithmicBoundary.Construction.extendEtaleRingDerivation_relative_logarithmic (S := V) k w ⟨D, hD⟩)

theorem refinedNormalDerivation_relative_logarithmic
    (w : ι → A) (D : Derivation k A A) (hD : D ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w) (z : A)
    (f : DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) :
    refinedNormalDerivation D z f ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k
      (fun j => algebraMap A (Localization.Away f) (w j)) := by
  have hN := normalizedNeighborhoodDerivation_relative_logarithmic w D hD z
  have h := Relative.LogarithmicBoundary.Construction.extendEtaleRingDerivation_relative_logarithmic (S := Localization.Away f) k
    (fun j => algebraMap A (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) (w j))
    ⟨NeighborhoodCoefficientOrder.Construction.normalizedNeighborhoodDerivation D z, hN⟩
  have he : (fun j => algebraMap (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) (Localization.Away f)
      (algebraMap A (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) (w j))) =
      (fun j => algebraMap A (Localization.Away f) (w j)) := by
    funext j
    exact (IsScalarTower.algebraMap_apply A (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) (Localization.Away f) (w j)).symm
  rw [he] at h
  exact h

variable [Algebra ℚ A] [IsNoetherianRing A]

/-- The further open chosen for the transverse coordinates retains
the strict dimension drop on its actual coefficient hypersurface. -/
theorem refinedNormalHypersurface_dimension_induction (D : Derivation k A A) (z : A)
    (f : DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) (d : ℕ) (hd : ringKrullDim A ≤ (d + 1 : ℕ)) :
    ringKrullDim (Localization.Away f ⧸ Ideal.span {algebraMap A (Localization.Away f) z}) ≤ d := by
  have hdim : ringKrullDim (Localization.Away f) ≤ ringKrullDim A :=
    (HypersurfaceDimension.Construction.localization_ringKrullDim_le (B := Localization.Away f) (Submonoid.powers f)).trans
      (HypersurfaceDimension.Construction.localization_ringKrullDim_le (B := DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) (Submonoid.powers (D z)))
  exact Coordinate.HypersurfaceDimension.Construction.coordinateHypersurface_dimension_induction (refinedNormalDerivation D z f)
    (algebraMap A (Localization.Away f) z) (refinedNormalDerivation_equation D z f) d (hdim.trans hd)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.RefinedNormalDerivative.Construction
