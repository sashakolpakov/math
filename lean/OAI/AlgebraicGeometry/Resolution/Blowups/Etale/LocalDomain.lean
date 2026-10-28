import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoordinateCenterReduced

/-! # Local Domain -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.LocalDomain.Construction

noncomputable section

/-! The actual closed local rings of étale coordinate charts and centers are domains. -/

section

variable {σ K S : Type*} [Field K] [IsAlgClosed K] [CommRing S] [Finite σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

include σ K in
/-- Exact multiplicativity of local order rules out zero divisors in the
closed local rings, including when the ambient étale algebra is disconnected. -/
theorem etale_closed_localRing_isDomain (q : Ideal S) [q.IsMaximal] :
    IsDomain (Localization.AtPrime q) := by
  obtain ⟨x, hx⟩ := ClosedOrder.Construction.finiteType_maximalIdeal_liesOver_polynomialPoint (K := K) (σ := σ) q
  let : q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x) := hx
  let : NoZeroDivisors (Localization.AtPrime q) := ⟨by
    intro s t hst
    by_contra h
    push Not at h
    obtain ⟨a, ha, ha1⟩ := PowerOrder.Construction.etale_local_exists_exact_order (σ := σ) (K := K) q s h.1
    obtain ⟨b, hb, hb1⟩ := PowerOrder.Construction.etale_local_exists_exact_order (σ := σ) (K := K) q t h.2
    have hprod := (MultiplicativeOrder.Construction.etale_local_exact_order_mul x q s t a b ha ha1 hb hb1).2
    rw [hst] at hprod
    exact hprod (Ideal.zero_mem _)⟩
  exact NoZeroDivisors.to_isDomain _

end

universe u

variable {σ K S : Type u} [Field K] [IsAlgClosed K] [CommRing S] [Finite σ] [DecidableEq σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

/-- Every closed local ring of an actual coordinate center is a domain. -/
theorem etale_coordinate_center_localRing_isDomain (C : Finset σ)
    (q : Ideal (S ⧸ (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S)))
    [q.IsMaximal] : IsDomain (Localization.AtPrime q) := by
  let A := S ⧸ (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S)
  let : Algebra (MvPolynomial {j : σ // j ∉ C} K) A :=
    (CoordinateHypersurfaceMap.Construction.etaleSubsetCenterMap (R := K) (S := S) C).toAlgebra
  let : Algebra.Etale (MvPolynomial {j : σ // j ∉ C} K) A :=
    CoordinateHypersurfaceMap.Construction.etaleSubsetCenterMap_etale C
  exact etale_closed_localRing_isDomain (σ := {j : σ // j ∉ C}) (K := K) q

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.LocalDomain.Construction
