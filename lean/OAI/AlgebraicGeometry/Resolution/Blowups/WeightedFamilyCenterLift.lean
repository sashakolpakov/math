import OAI.AlgebraicGeometry.Resolution.Blowups.WeightedGeneratorFamily
import OAI.AlgebraicGeometry.Resolution.Blowups.WeightedCoefficientCenterLift

/-! # Weighted Family Center Lift -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.WeightedFamilyCenterLift.Construction

noncomputable section

/-! Center lifting for fixed coefficient families and arbitrary coordinate derivations. -/

universe u

variable {σ K S : Type u} [Field K] [IsAlgClosed K] [CharZero K] [CommRing S]
  [Finite σ] [DecidableEq σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]
variable {k ι : Type*} [CommRing k] [Algebra k S]

/-- A fixed generator family's weighted coefficient center is permissible
exactly when its ambient ideal is. The derivation need only take the chosen
hypersurface coordinate to one, so this applies to the derivation carried
through a preceding blowup. -/
theorem etale_coordinate_center_iff_weighted_family_center
    (C : Finset σ) (h : σ) (hh : h ∈ C) (D : Derivation k S S)
    (hD : D (algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)) = 1)
    (p : ι → S) (b : ℕ) :
    let I := (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S)
    let z := algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)
    Ideal.span (Set.range p) ≤ I ^ b ↔ WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal D z p b ≤
      I.map (Ideal.Quotient.mk (Ideal.span {z})) ^ b.factorial := by
  let : Algebra ℚ S := ((algebraMap (MvPolynomial σ K) S).comp
    ((MvPolynomial.C : K →+* MvPolynomial σ K).comp (algebraMap ℚ K))).toAlgebra
  let I := (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S)
  let z := algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)
  have hzI : z ∈ I := Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨h, hh, rfl⟩)
  obtain ⟨φ, hφ, _⟩ := Blowups.Etale.CoordinateHypersurfaceMap.Construction.etaleCoordinateHypersurface_exists_coordinates (R := K) (S := S) h
  let : Algebra (MvPolynomial {j : σ // j ∉ ({h} : Finset σ)} K)
      (S ⧸ Ideal.span {z}) := φ.toAlgebra
  let : Algebra.Etale (MvPolynomial {j : σ // j ∉ ({h} : Finset σ)} K)
      (S ⧸ Ideal.span {z}) := hφ
  change Ideal.span (Set.range p) ≤ I ^ b ↔ WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal D z p b ≤
    I.map (Ideal.Quotient.mk (Ideal.span {z})) ^ b.factorial
  constructor
  · intro hp
    have hcoeff := (HypersurfaceCoefficientTransform.Construction.span_order_iff_coordinateDerivativeFamilyIdeals D z hD p I hzI b).mp hp
    exact WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal_le_pow _ b _ (fun j => hcoeff j.val j.isLt)
  · intro hcoeff
    cases b with
    | zero => simp only [pow_zero, Ideal.one_eq_top, le_top]
    | succ b =>
      apply (Coordinate.CenterPermissibility.Construction.etale_coordinate_center_permissible_iff_closedPoint_order C (Ideal.span (Set.range p)) b).mpr
      intro M _ hIM
      rw [ClosedWeightedOrder.Construction.closedPoint_local_order_iff]
      apply (WeightedGeneratorFamily.Construction.closedPoint_span_order_iff_weighted_family
        (σ := {j : σ // j ∉ ({h} : Finset σ)}) (K := K) D z hD p M (hIM hzI) (b + 1)).mpr
      exact hcoeff.trans (pow_le_pow_left' (Ideal.map_mono hIM) (b + 1).factorial)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.WeightedFamilyCenterLift.Construction
