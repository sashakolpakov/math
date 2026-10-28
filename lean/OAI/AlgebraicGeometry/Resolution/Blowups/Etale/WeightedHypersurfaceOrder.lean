import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedWeightedOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoordinateHypersurfaceMap
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoefficientStep

/-! # Weighted Hypersurface Order -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.WeightedHypersurfaceOrder.Construction

noncomputable section

/-! The weighted order reduction on actual coordinate hypersurfaces of étale charts. -/

universe u

variable {σ K S : Type u} [Field K] [IsAlgClosed K] [CharZero K] [CommRing S]
  [Finite σ] [DecidableEq σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

/-- Any selected coordinate of an étale ambient chart supplies an actual
weighted ideal on its quotient hypersurface, detecting local order at every
closed point on that hypersurface. -/
theorem etale_coordinate_local_order_iff_weighted_coefficients
    (h : σ) (J q : Ideal S) [q.IsMaximal]
    (hhq : algebraMap (MvPolynomial σ K) S (MvPolynomial.X h) ∈ q) (b : ℕ) :
    J.map (algebraMap S (Localization.AtPrime q)) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ b ↔
      ClosedWeightedOrder.Construction.weightedDifferentialCoefficientIdeal (LocalOrder.Construction.etalePolynomialCoordinateDerivation (K := K) h)
        (algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)) J b ≤
        q.map (Ideal.Quotient.mk
          (Ideal.span {algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)})) ^ b.factorial := by
  let : Algebra ℚ S := ((algebraMap (MvPolynomial σ K) S).comp
    ((MvPolynomial.C : K →+* MvPolynomial σ K).comp (algebraMap ℚ K))).toAlgebra
  obtain ⟨φ, hφ, _⟩ := CoordinateHypersurfaceMap.Construction.etaleCoordinateHypersurface_exists_coordinates (R := K) (S := S) h
  let : Algebra (MvPolynomial {j : σ // j ∉ ({h} : Finset σ)} K)
      (S ⧸ Ideal.span {algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)}) := φ.toAlgebra
  let : Algebra.Etale (MvPolynomial {j : σ // j ∉ ({h} : Finset σ)} K)
      (S ⧸ Ideal.span {algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)}) := hφ
  apply ClosedWeightedOrder.Construction.closedPoint_local_order_iff_weightedDifferentialCoefficients
    (σ := {j : σ // j ∉ ({h} : Finset σ)}) (K := K) _ _ _ J q hhq b
  have hd := CoefficientStep.Construction.etalePolynomialCoordinateDerivation_X (K := K) (S := S) h h
  rw [ite_eq_left rfl] at hd
  exact hd

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.WeightedHypersurfaceOrder.Construction
