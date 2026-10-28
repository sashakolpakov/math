import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.PowerOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ClosedOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoordinateHypersurfaceMap
import Mathlib.RingTheory.LocalProperties.Reduced

/-! # Coordinate Center Reduced -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoordinateCenterReduced.Construction

noncomputable section

/-! Reducedness of the actual coordinate centers used in permissible blowups. -/

section

variable {σ K S : Type*} [Field K] [IsAlgClosed K] [CommRing S] [Finite σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

include σ K in
/-- Exact order of powers rules out nilpotents in every closed local ring. -/
theorem etale_closed_localRing_isReduced (q : Ideal S) [q.IsMaximal] :
    IsReduced (Localization.AtPrime q) := by
  obtain ⟨x, hx⟩ := ClosedOrder.Construction.finiteType_maximalIdeal_liesOver_polynomialPoint (K := K) (σ := σ) q
  let : q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x) := hx
  constructor
  intro s hs
  by_contra hsz
  obtain ⟨d, hd, hd1⟩ := PowerOrder.Construction.etale_local_exists_exact_order (σ := σ) (K := K) q s hsz
  obtain ⟨e, he⟩ := hs
  have hne := (PowerOrder.Construction.etale_local_exact_order_pow x q s d e hd hd1).2
  rw [he] at hne
  exact hne (Ideal.zero_mem _)

include σ K in
/-- Reducedness for an arbitrary étale polynomial algebra, without an
integrality assumption on the algebra. -/
theorem etale_polynomial_isReduced : IsReduced S := by
  constructor
  intro s hs
  apply eq_zero_of_localization s
  intro q hq
  let : IsReduced (Localization.AtPrime q) := etale_closed_localRing_isReduced (σ := σ) (K := K) q
  exact (hs.map (algebraMap S (Localization.AtPrime q))).eq_zero

end

universe u

variable {σ K S : Type u} [Field K] [IsAlgClosed K] [CommRing S] [Finite σ] [DecidableEq σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

/-- Every selected coordinate center is reduced, including disconnected centers. -/
theorem etaleSubsetCoordinateCenter_isReduced (C : Finset σ) :
    IsReduced (S ⧸ (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S)) := by
  let : Algebra (MvPolynomial {j : σ // j ∉ C} K)
      (S ⧸ (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S)) :=
    (CoordinateHypersurfaceMap.Construction.etaleSubsetCenterMap (R := K) (S := S) C).toAlgebra
  let : Algebra.Etale (MvPolynomial {j : σ // j ∉ C} K)
      (S ⧸ (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S)) :=
    CoordinateHypersurfaceMap.Construction.etaleSubsetCenterMap_etale C
  exact etale_polynomial_isReduced (σ := {j : σ // j ∉ C}) (K := K)

theorem etaleSubsetCoordinateIdeal_isRadical (C : Finset σ) :
    ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S)).IsRadical :=
  (Ideal.isRadical_iff_quotient_reduced _).mpr (etaleSubsetCoordinateCenter_isReduced C)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CoordinateCenterReduced.Construction
