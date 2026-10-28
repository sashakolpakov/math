import OAI.AlgebraicGeometry.Resolution.Blowups.Quotient.SmoothCenterLift
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.CoefficientFamilyInterval

/-! # Coefficient Family Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoefficientFamilyCenter.Construction

noncomputable section

/-! Retained coefficient families detect every smooth permissible center, without choosing center coordinates. -/

universe u

variable (k : Type u) {R : Type u} {τ : Type*}
  [Field k] [CharZero k] [IsAlgClosed k] [CommRing R] [Algebra k R] [Algebra ℚ R]
  [Algebra.Smooth k R]

theorem smooth_center_iff_weighted_normal_family
    (I : Ideal R) [Algebra.Smooth k (R ⧸ I)] (z : R) (hzI : z ∈ I)
    (D : Derivation k R R) (hD : D z = 1) (p : τ → R) (b : ℕ) :
    Ideal.span (Set.range p) ≤ I ^ b ↔ WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal D z p b ≤
      I.map (Ideal.Quotient.mk (Ideal.span {z})) ^ b.factorial := by
  let Q := R ⧸ Ideal.span {z}
  let K := I.map (Ideal.Quotient.mk (Ideal.span {z}))
  let : Algebra.Smooth k Q := DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one D z hD
  let : Algebra.Smooth k (Q ⧸ K) := Algebra.Smooth.of_equiv
    (DoubleQuot.quotQuotEquivQuotOfLEₐ k ((Ideal.span_singleton_le_iff_mem I).mpr hzI)).symm
  constructor
  · intro hp
    have hcoeff := (HypersurfaceCoefficientTransform.Construction.span_order_iff_coordinateDerivativeFamilyIdeals D z hD p I hzI b).mp hp
    exact WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal_le_pow K b _ (fun j => hcoeff j.val j.isLt)
  · intro hC
    have hcoeff := (CenterPowerRoot.Construction.smooth_center_weighted_iff k K b
      (fun j => HypersurfaceCoefficientTransform.Construction.coordinateDerivativeFamilyIdeal D z p j.val)).mp hC
    apply (HypersurfaceCoefficientTransform.Construction.span_order_iff_coordinateDerivativeFamilyIdeals D z hD p I hzI b).mpr
    intro j hj
    exact hcoeff ⟨j, hj⟩

/-- Every retained coefficient ideal between the fixed normal family and the
intrinsic relative coefficients has exactly the same permissible smooth centers. -/
theorem smooth_center_iff_coefficient_family_interval
    (I : Ideal R) [Algebra.Smooth k (R ⧸ I)] (z : R) (hzI : z ∈ I)
    (D : Derivation k R R) (hD : D z = 1) (p : τ → R) (b : ℕ)
    (C : Ideal (R ⧸ Ideal.span {z}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal D z p b ≤ C)
    (hupp : C ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Ideal.span (Set.range p)) b) :
    Ideal.span (Set.range p) ≤ I ^ b ↔ C ≤ I.map (Ideal.Quotient.mk (Ideal.span {z})) ^ b.factorial := by
  constructor
  · intro hp
    exact hupp.trans (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal_le_of_order k z (Ideal.span (Set.range p)) I b hp)
  · intro hC
    exact (smooth_center_iff_weighted_normal_family k I z hzI D hD p b).mpr (hlow.trans hC)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoefficientFamilyCenter.Construction
