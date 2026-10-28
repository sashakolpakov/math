import OAI.AlgebraicGeometry.Resolution.Blowups.NeighborhoodCoefficientOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.Regularity
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-! # Hypersurface Dimension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfaceDimension.Construction

noncomputable section

/-! Dimension reduction for the actual derivative hypersurface neighborhood. -/

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- Localization cannot increase Krull dimension: contraction embeds
chains of prime ideals into chains in the original ring. -/
theorem localization_ringKrullDim_le (M : Submonoid A) [IsLocalization M B] :
    ringKrullDim B ≤ ringKrullDim A := by
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B))
  intro p q hpq
  exact (IsLocalization.orderEmbedding M B).strictMono hpq

variable {k : Type*} [CommRing k] [Algebra k A] [Algebra ℚ A] [IsNoetherianRing A]

/-- The hypersurface equation is a non-zero-divisor on the chosen
ambient neighborhood, including when the original algebra is not integral. -/
theorem differentialHypersurfaceNeighborhood_equation_regular (D : Derivation k A A) (z : A) :
    IsRegular (algebraMap A (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) z) := by
  apply Coordinate.Regularity.Construction.coordinate_isRegular (NeighborhoodCoefficientOrder.Construction.normalizedNeighborhoodDerivation D z)
  exact NeighborhoodCoefficientOrder.Construction.normalizedNeighborhoodDerivation_equation D z

/-- Passing to the actual hypersurface drops dimension by at least one. -/
theorem differentialHypersurfaceNeighborhood_dimension_drop (D : Derivation k A A) (z : A) :
    ringKrullDim (DifferentialHypersurfaceNeighborhood.Construction.differentialHypersurfaceNeighborhood D z) + 1 ≤
      ringKrullDim (DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) :=
  ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (differentialHypersurfaceNeighborhood_equation_regular D z).mem_nonZeroDivisors

/-- The dimension bound also holds relative to the original ambient algebra. -/
theorem differentialHypersurfaceNeighborhood_dimension_bound (D : Derivation k A A) (z : A) :
    ringKrullDim (DifferentialHypersurfaceNeighborhood.Construction.differentialHypersurfaceNeighborhood D z) + 1 ≤ ringKrullDim A :=
  (differentialHypersurfaceNeighborhood_dimension_drop D z).trans
    (localization_ringKrullDim_le (B := DifferentialHypersurfaceNeighborhood.Construction.derivationNeighborhood D z) (Submonoid.powers (D z)))

/-- A natural-number bound on ambient dimension decreases by one,
giving the dimension parameter for induction on the hypersurface. -/
theorem differentialHypersurfaceNeighborhood_dimension_induction (D : Derivation k A A)
    (z : A) (d : ℕ) (hd : ringKrullDim A ≤ (d + 1 : ℕ)) :
    ringKrullDim (DifferentialHypersurfaceNeighborhood.Construction.differentialHypersurfaceNeighborhood D z) ≤ d := by
  have h := (differentialHypersurfaceNeighborhood_dimension_bound D z).trans hd
  rw [Nat.cast_add, Nat.cast_one] at h
  exact ENat.WithBot.add_le_add_one_right_iff.mp h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfaceDimension.Construction
