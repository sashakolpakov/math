import OAI.AlgebraicGeometry.Resolution.Blowups.ZeroDimensionalCanonicalCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.CoefficientFamilyInterval
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Zero Dimensional Hypersurface Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ZeroDimensionalHypersurfaceCenter.Construction

noncomputable section

/-! Centers inside a smooth zero-dimensional hypersurface in the original ambient ring. -/

universe u

variable (k : Type u) {R : Type u} [CommRing k] [CommRing R] [Algebra k R]

/-- Every closed center inside a smooth reduced zero-dimensional hypersurface
is smooth over the original base, without an ambient retraction. -/
theorem zero_dimensional_hypersurface_center_smooth (z : R)
    [Algebra.Smooth k (R ⧸ Ideal.span {z})]
    [IsNoetherianRing (R ⧸ Ideal.span {z})] [IsReduced (R ⧸ Ideal.span {z})]
    (hd : ringKrullDim (R ⧸ Ideal.span {z}) ≤ 0) (I : Ideal R) (hz : z ∈ I) :
    Algebra.Smooth k (R ⧸ I) := by
  let H := R ⧸ Ideal.span {z}
  let C := I.map (Ideal.Quotient.mkₐ k (Ideal.span {z}))
  let : Algebra.Etale H (H ⧸ C) := ZeroDimensionalCoefficientCenter.Construction.zero_dimensional_ideal_quotient_etale hd C
  let : Algebra.Smooth k (H ⧸ C) := Algebra.Smooth.comp k H (H ⧸ C)
  exact Algebra.Smooth.of_equiv
    (DoubleQuot.quotQuotEquivQuotOfLEₐ k ((Ideal.span_singleton_le_iff_mem I).mpr hz))

/-- The intrinsic tangent ideal is a permissible smooth center whenever it
contains a coordinate whose smooth hypersurface has dimension zero. -/
theorem zero_dimensional_hypersurface_intrinsic_center [Algebra ℚ R]
    (D : Derivation k R R) (z : R) (hD : D z = 1)
    [Algebra.Smooth k (R ⧸ Ideal.span {z})]
    [IsNoetherianRing (R ⧸ Ideal.span {z})] [IsReduced (R ⧸ Ideal.span {z})]
    (hd : ringKrullDim (R ⧸ Ideal.span {z}) ≤ 0) (J : Ideal R) (n : ℕ)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) :
    J ≤ (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) ^ (n + 1) ∧
      Algebra.Smooth k (R ⧸ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) := by
  let p : J → R := Subtype.val
  have hspan : Ideal.span (Set.range p) = J := by
    rw [Subtype.range_val, Ideal.span_eq]
  let C := Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Ideal.span (Set.range p)) (n + 1)
  have hlow := Relative.CoefficientFamilyInterval.Construction.weightedCoordinateDerivativeFamilyIdeal_le_relative k D z p (n + 1)
  have hzp : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Ideal.span (Set.range p)) n := by
    rw [hspan]
    exact hz
  have hcenter := ZeroDimensionalCanonicalCenter.Construction.zero_dimensional_coefficient_center_eq_tangent k D z hD hd p n hzp C hlow le_rfl
  have hperm := ZeroDimensionalCoefficientPermissibility.Construction.zero_dimensional_coefficient_center_permissible D z hD hd p (n + 1) C hlow
  rw [hcenter, hspan] at hperm
  exact ⟨hperm, zero_dimensional_hypersurface_center_smooth k z hd _ hz⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ZeroDimensionalHypersurfaceCenter.Construction
