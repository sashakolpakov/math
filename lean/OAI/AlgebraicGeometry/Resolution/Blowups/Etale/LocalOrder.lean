import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.LocalCoordinates
import OAI.AlgebraicGeometry.Resolution.Blowups.MappedEulerOrderCriterion
import OAI.AlgebraicGeometry.Resolution.Blowups.PersistentHypersurface

/-! # Local Order -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.LocalOrder.Construction

noncomputable section

/-! Differential equations detect local ideal order on étale affine neighborhoods. -/

open _root_.MvPolynomial

variable {σ K S : Type*} [Field K] [CommRing S]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

def etaleCenteredCoordinate (x : σ → K) (i : σ) : S :=
  algebraMap (MvPolynomial σ K) S (X i - C (x i))

def etalePolynomialCoordinateDerivation (i : σ) : Derivation ℤ S S :=
  Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) (PersistentHypersurface.Construction.polynomialPartialDerivationInt (R := K) i)

theorem etalePolynomialCoordinateDerivation_centered [DecidableEq σ] (x : σ → K) (i j : σ) :
    etalePolynomialCoordinateDerivation (K := K) (S := S) i (etaleCenteredCoordinate (S := S) x j) =
      if i = j then 1 else 0 := by
  change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := S) (PersistentHypersurface.Construction.polynomialPartialDerivationInt (R := K) i)
    (algebraMap (MvPolynomial σ K) S (X j - C (x j))) = _
  rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap]
  change algebraMap (MvPolynomial σ K) S (pderiv i (X j - C (x j))) = _
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Ne.symm hij]

variable [CharZero K] [Fintype σ] [DecidableEq σ]

/-- For any ideal of an étale polynomial algebra, its order in the actual
local ring at a rational point is detected by the differential ideal on
the original affine algebra. The ideal need not descend to the polynomial base. -/
theorem etale_local_order_iff_differentialIdeal (J : Ideal S) (x : σ → K)
    (q : Ideal S) [q.IsPrime] [q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x)] (b : ℕ) :
    J.map (algebraMap S (Localization.AtPrime q)) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (b + 1) ↔
      DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J b ≤ q := by
  let T := Localization.AtPrime q
  let : Algebra ℚ T :=
    ((algebraMap (MvPolynomial σ K) T).comp ((C : K →+* MvPolynomial σ K).comp (algebraMap ℚ K))).toAlgebra
  let : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_isLocalization q.primeCompl
  let z : σ → S := etaleCenteredCoordinate x
  let D : σ → Derivation ℤ S S := etalePolynomialCoordinateDerivation (K := K) (S := S)
  have hD : ∀ i j, D i (z j) = if i = j then 1 else 0 :=
    etalePolynomialCoordinateDerivation_centered x
  have hM : Ideal.span (Set.range (fun i => algebraMap S T (z i))) = IsLocalRing.maximalIdeal T := by
    rw [LocalCoordinates.Construction.etale_local_maximalIdeal_eq_span_coordinates x q]
    apply congrArg (fun f : σ → T => Ideal.span (Set.range f))
    funext i
    exact (IsScalarTower.algebraMap_apply (MvPolynomial σ K) S T (X i - C (x i))).symm
  have h := MappedEulerOrderCriterion.Construction.mapped_coordinate_order_iff_differentialIdeal (B := T) z D hD J b
  rw [hM] at h
  have hq : (IsLocalRing.maximalIdeal T).comap (algebraMap S T) = q :=
    Localization.AtPrime.under_maximalIdeal (I := q)
  simpa only [Ideal.map_le_iff_le_comap, hq] using h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.LocalOrder.Construction
