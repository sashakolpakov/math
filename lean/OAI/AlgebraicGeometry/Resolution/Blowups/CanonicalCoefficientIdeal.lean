import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedWeightedOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialIdealTransform

/-! # Canonical Coefficient Ideal -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalCoefficientIdeal.Construction

noncomputable section

/-! A hypersurface coefficient ideal formed from all derivations, with
no choice of a transverse derivative in its definition. -/

variable {R : Type*} [CommRing R]

/-- The canonical coefficient ideal uses the full differential ideals
at their natural controls, combined at factorial control. -/
def canonicalCoefficientIdeal (z : R) (J : Ideal R) (b : ℕ) :
    Ideal (R ⧸ Ideal.span {z}) :=
  WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b (fun j =>
    (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J j.val).map (Ideal.Quotient.mk (Ideal.span {z})))

theorem iterated_ring_derivation_mem_differential
    (D : Derivation ℤ R R) (J : Ideal R) (p : R) (hp : p ∈ J) (n : ℕ) :
    D^[n] p ∈ DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J n := by
  induction n generalizing J p with
  | zero => exact hp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih (DifferentialIdealTransform.Construction.firstDifferentialIdeal J) (D p) (DifferentialIdealTransform.Construction.derivation_mem_firstDifferentialIdeal J D hp)

theorem differentialCoefficientIdeal_le_full_differential
    (D : Derivation ℤ R R) (z : R) (J : Ideal R) (n : ℕ) :
    DifferentialCoefficientOrder.Construction.differentialCoefficientIdeal D z J n ≤
      (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J n).map (Ideal.Quotient.mk (Ideal.span {z})) := by
  apply Ideal.span_le.mpr
  rintro x ⟨p, rfl⟩
  exact Ideal.mem_map_of_mem _ (iterated_ring_derivation_mem_differential D J p.val p.property n)

/-- Every coefficient ideal made with a chosen transverse derivation
is contained in the canonical one. -/
theorem weightedDifferentialCoefficientIdeal_le_canonical
    (D : Derivation ℤ R R) (z : R) (J : Ideal R) (b : ℕ) :
    ClosedWeightedOrder.Construction.weightedDifferentialCoefficientIdeal D z J b ≤ canonicalCoefficientIdeal z J b := by
  unfold ClosedWeightedOrder.Construction.weightedDifferentialCoefficientIdeal canonicalCoefficientIdeal WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal
  exact iSup_mono (fun j => pow_le_pow_left'
    (differentialCoefficientIdeal_le_full_differential D z J j.val) (WeightedCoefficientIdeal.Construction.coefficientWeight b j))

/-- Ambient order supplies the canonical coefficient bound at every
ideal, independently of any choice of transverse derivative. -/
theorem canonicalCoefficientIdeal_le_of_order
    (z : R) (J q : Ideal R) (b : ℕ) (hJ : J ≤ q ^ b) :
    canonicalCoefficientIdeal z J b ≤
      q.map (Ideal.Quotient.mk (Ideal.span {z})) ^ b.factorial := by
  apply WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal_le_pow
  intro j
  have hdiff : DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J j.val ≤ q ^ (b - j.val) :=
    DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow q J (b - j.val) j.val
      (by simpa only [Nat.sub_add_cancel (Nat.le_of_lt j.isLt)] using hJ)
  simpa only [Ideal.map_pow] using Ideal.map_mono (f := Ideal.Quotient.mk (Ideal.span {z})) hdiff

variable {σ K : Type*} [Field K] [IsAlgClosed K] [Finite σ] [Algebra ℚ R]

include σ K in
/-- On an actual étale coordinate hypersurface, the canonical ideal has
exactly the ambient order locus. A transverse derivative proves the
equivalence but is not part of the coefficient ideal itself. -/
theorem closedPoint_order_iff_canonical_coefficients
    (D : Derivation ℤ R R) (z : R) (hz : D z = 1)
    [Algebra (MvPolynomial σ K) (R ⧸ Ideal.span {z})]
    [Algebra.Etale (MvPolynomial σ K) (R ⧸ Ideal.span {z})]
    (J q : Ideal R) [q.IsMaximal] (hzq : z ∈ q) (b : ℕ) :
    J ≤ q ^ b ↔ canonicalCoefficientIdeal z J b ≤
      q.map (Ideal.Quotient.mk (Ideal.span {z})) ^ b.factorial := by
  constructor
  · exact canonicalCoefficientIdeal_le_of_order z J q b
  · intro h
    apply (ClosedWeightedOrder.Construction.closedPoint_order_iff_weightedDifferentialCoefficients (σ := σ) (K := K)
      D z hz J q hzq b).mpr
    exact (weightedDifferentialCoefficientIdeal_le_canonical D z J b).trans h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalCoefficientIdeal.Construction
