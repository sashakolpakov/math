import OAI.AlgebraicGeometry.Resolution.Blowups.ZeroDimensionalCoefficientPermissibility
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.UnitCriterion

/-! # Zero Dimensional Canonical Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ZeroDimensionalCanonicalCenter.Construction

noncomputable section

/-! In coefficient dimension zero, the selected ambient center is the intrinsic tangent ideal. -/

private theorem zero_dimensional_ideal_pow_pos {H : Type*} [CommRing H]
    [IsNoetherianRing H] [IsReduced H] (hd : ringKrullDim H ≤ 0)
    (C : Ideal H) (b : ℕ) (hb : 0 < b) : C ^ b = C := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  exact ZeroDimensionalCoefficientCenter.Construction.zero_dimensional_ideal_pow hd C n

variable (k : Type*) {R : Type*} [CommRing k] [CommRing R] [Algebra k R]

/-- All coefficient powers are idempotent in dimension zero, so the
intrinsic coefficient ideal is exactly the image of the last differential ideal. -/
theorem zero_dimensional_relative_coefficients_eq_tangent_image (z : R)
    [IsNoetherianRing (R ⧸ Ideal.span {z})] [IsReduced (R ⧸ Ideal.span {z})]
    (hd : ringKrullDim (R ⧸ Ideal.span {z}) ≤ 0) (J : Ideal R) (n : ℕ) :
    Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J (n + 1) =
      (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map (Ideal.Quotient.mk (Ideal.span {z})) := by
  apply le_antisymm (Coefficient.UnitCriterion.Construction.relativeCoefficientIdeal_le_tangent_image k z J n)
  let i : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
  have h := le_iSup (fun j : Fin (n + 1) =>
    ((Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val).map (Ideal.Quotient.mk (Ideal.span {z}))) ^
      WeightedCoefficientIdeal.Construction.coefficientWeight (n + 1) j) i
  have hp := zero_dimensional_ideal_pow_pos hd
    ((Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map (Ideal.Quotient.mk (Ideal.span {z})))
    (WeightedCoefficientIdeal.Construction.coefficientWeight (n + 1) i) (WeightedCoefficientIdeal.Construction.coefficientWeight_pos (n + 1) i)
  change ((Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map (Ideal.Quotient.mk (Ideal.span {z}))) ^
    WeightedCoefficientIdeal.Construction.coefficientWeight (n + 1) i ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J (n + 1) at h
  rw [hp] at h
  exact h

variable [Algebra ℚ R]

/-- In coefficient dimension zero, every retained coefficient interval
collapses to the intrinsic coefficient ideal itself. -/
theorem zero_dimensional_coefficient_interval_eq_relative {ι : Type*}
    (D : Derivation k R R) (z : R) (hD : D z = 1)
    [IsNoetherianRing (R ⧸ Ideal.span {z})] [IsReduced (R ⧸ Ideal.span {z})]
    (hd : ringKrullDim (R ⧸ Ideal.span {z}) ≤ 0) (p : ι → R) (n : ℕ)
    (C : Ideal (R ⧸ Ideal.span {z}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal D z p (n + 1) ≤ C)
    (hupp : C ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Ideal.span (Set.range p)) (n + 1)) :
    C = Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Ideal.span (Set.range p)) (n + 1) := by
  let I := C.comap (Ideal.Quotient.mk (Ideal.span {z}))
  have hperm := ZeroDimensionalCoefficientPermissibility.Construction.zero_dimensional_coefficient_center_permissible D z hD hd p (n + 1) C hlow
  have hbound := Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal_le_of_order k z (Ideal.span (Set.range p)) I (n + 1) hperm
  have hmap : I.map (Ideal.Quotient.mk (Ideal.span {z})) = C :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective C
  rw [hmap, zero_dimensional_ideal_pow_pos hd C (n + 1).factorial (Nat.factorial_pos _)] at hbound
  exact le_antisymm hupp hbound

/-- The actual ambient center in this base case is the original intrinsic
tangent ideal. It is independent of the retraction and normal derivative choices. -/
theorem zero_dimensional_coefficient_center_eq_tangent {ι : Type*}
    (D : Derivation k R R) (z : R) (hD : D z = 1)
    [IsNoetherianRing (R ⧸ Ideal.span {z})] [IsReduced (R ⧸ Ideal.span {z})]
    (hd : ringKrullDim (R ⧸ Ideal.span {z}) ≤ 0) (p : ι → R) (n : ℕ)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Ideal.span (Set.range p)) n)
    (C : Ideal (R ⧸ Ideal.span {z}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal D z p (n + 1) ≤ C)
    (hupp : C ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Ideal.span (Set.range p)) (n + 1)) :
    C.comap (Ideal.Quotient.mk (Ideal.span {z})) =
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Ideal.span (Set.range p)) n := by
  let q := Ideal.Quotient.mk (Ideal.span {z})
  let T := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Ideal.span (Set.range p)) n
  have hC : C = T.map q :=
    (zero_dimensional_coefficient_interval_eq_relative k D z hD hd p n C hlow hupp).trans
      (zero_dimensional_relative_coefficients_eq_tangent_image k z hd (Ideal.span (Set.range p)) n)
  have hker : RingHom.ker q ≤ T := by
    rw [Ideal.mk_ker]
    exact (Ideal.span_singleton_le_iff_mem T).mpr hz
  have hrecover := Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective T
  rw [← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker] at hrecover
  exact (congrArg (Ideal.comap q) hC).trans hrecover

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ZeroDimensionalCanonicalCenter.Construction
