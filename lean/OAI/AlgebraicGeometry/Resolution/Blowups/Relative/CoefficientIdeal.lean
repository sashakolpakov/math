import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedWeightedOrder

/-! # Coefficient Ideal -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Relative.CoefficientIdeal.Construction

noncomputable section

/-! Intrinsic hypersurface coefficients relative to the fixed coefficient ring. -/

variable (k : Type*) {R : Type*} [CommRing k] [CommRing R] [Algebra k R]

/-- The coefficient ideal built from all relative differential ideals. -/
def relativeCoefficientIdeal (z : R) (J : Ideal R) (b : ℕ) : Ideal (R ⧸ Ideal.span {z}) :=
  WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b (fun j =>
    (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val).map (Ideal.Quotient.mk (Ideal.span {z})))

theorem iterated_relative_derivation_mem_differential
    (D : Derivation k R R) (J : Ideal R) (p : R) (hp : p ∈ J) (n : ℕ) :
    D^[n] p ∈ DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n := by
  induction n generalizing J p with
  | zero => exact hp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih (DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k J) (D p) (DifferentialBlowup.Construction.relative_derivation_mem_first k J D hp)

/-- Coefficients formed using any one relative derivation are contained
in the intrinsic relative coefficient ideal. -/
theorem weightedDifferentialCoefficientIdeal_le_relative
    (D : Derivation k R R) (z : R) (J : Ideal R) (b : ℕ) :
    ClosedWeightedOrder.Construction.weightedDifferentialCoefficientIdeal D z J b ≤ relativeCoefficientIdeal k z J b := by
  unfold ClosedWeightedOrder.Construction.weightedDifferentialCoefficientIdeal relativeCoefficientIdeal WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal
  apply iSup_mono
  intro j
  apply pow_le_pow_left'
  apply Ideal.span_le.mpr
  rintro x ⟨p, rfl⟩
  exact Ideal.mem_map_of_mem _
    (iterated_relative_derivation_mem_differential k D J p.val p.property j.val)

theorem relativeCoefficientIdeal_le_of_order
    (z : R) (J q : Ideal R) (b : ℕ) (hJ : J ≤ q ^ b) :
    relativeCoefficientIdeal k z J b ≤
      q.map (Ideal.Quotient.mk (Ideal.span {z})) ^ b.factorial := by
  apply WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal_le_pow
  intro j
  have hdiff : DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val ≤ q ^ (b - j.val) :=
    (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_le_ordinary k J j.val).trans
      (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow q J (b - j.val) j.val
        (by simpa only [Nat.sub_add_cancel (Nat.le_of_lt j.isLt)] using hJ))
  simpa only [Ideal.map_pow] using Ideal.map_mono (f := Ideal.Quotient.mk (Ideal.span {z})) hdiff

variable {σ K : Type*} [Field K] [IsAlgClosed K] [Finite σ] [Algebra ℚ R]

include σ K in
/-- The intrinsic relative coefficient ideal detects the exact
ambient order at closed points of an actual étale hypersurface. -/
theorem closedPoint_order_iff_relative_coefficients
    (D : Derivation k R R) (z : R) (hz : D z = 1)
    [Algebra (MvPolynomial σ K) (R ⧸ Ideal.span {z})]
    [Algebra.Etale (MvPolynomial σ K) (R ⧸ Ideal.span {z})]
    (J q : Ideal R) [q.IsMaximal] (hzq : z ∈ q) (b : ℕ) :
    J ≤ q ^ b ↔ relativeCoefficientIdeal k z J b ≤
      q.map (Ideal.Quotient.mk (Ideal.span {z})) ^ b.factorial := by
  constructor
  · exact relativeCoefficientIdeal_le_of_order k z J q b
  · intro h
    apply (ClosedWeightedOrder.Construction.closedPoint_order_iff_weightedDifferentialCoefficients (σ := σ) (K := K)
      D z hz J q hzq b).mpr
    exact (weightedDifferentialCoefficientIdeal_le_relative k D z J b).trans h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Relative.CoefficientIdeal.Construction
