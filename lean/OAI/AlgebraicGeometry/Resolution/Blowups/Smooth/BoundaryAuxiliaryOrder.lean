import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CompanionOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CountReduction
import OAI.AlgebraicGeometry.Resolution.Blowups.ResidualDropAllPrimes

/-! # Boundary Auxiliary Order -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.BoundaryAuxiliaryOrder.Construction

noncomputable section

/-! Intrinsic boundary auxiliary bounds, center conditions, and clearance on smooth algebras. -/

section

universe u

variable (k : Type u) {R : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  [CommRing R] [Algebra k R] [Algebra.Smooth k R]

/-- A boundary ideal of order at most one bounds its auxiliary marked
ideal at the prescribed control, independently of the residual ideal. -/
theorem smooth_boundary_auxiliary_differential_bound (J L : Ideal R) (m : ℕ) (hm : 0 < m)
    (hL : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k L 1 = ⊤) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Boundary.AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal J L m) m = ⊤ := by
  apply (ClosedPointChartTransport.Construction.smooth_relative_differential_bound_iff_closedPoint_bound k _ m).mpr
  intro q _ hq
  have hL2 : ¬ L ≤ q ^ (1 + 1) := by
    intro h
    exact ((ClosedPointChartTransport.Construction.smooth_relative_differential_bound_iff_closedPoint_bound k L 1).mp hL q)
      ((ClosedWeightedOrder.Construction.closedPoint_local_order_iff L q (1 + 1)).mpr h)
  have hpow : L ^ m ≤ q ^ (m + 1) := le_sup_right.trans
    ((ClosedWeightedOrder.Construction.closedPoint_local_order_iff _ q (m + 1)).mp hq)
  apply hL2
  exact (ProductOrder.Construction.smooth_closedPoint_power_strict_order_iff k L q 1 m hm).mp
    (by simpa only [one_mul] using hpow)

/-- Auxiliary clearance is exactly disjointness of the remaining
residual order locus from the selected boundary intersection. -/
theorem smooth_boundary_auxiliary_terminal_iff (J L : Ideal R) (m : ℕ) (hm : 0 < m) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Boundary.AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal J L m) (m - 1) = ⊤ ↔
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (m - 1) ⊔ L = ⊤ := by
  constructor
  · intro hclear
    by_contra hproper
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hproper
    let : q.IsMaximal := hq
    have hJ : J ≤ q ^ m := (CompanionOrder.Construction.smooth_closedPoint_order_iff_differential_control k J q m hm).mpr
      (le_sup_left.trans hle)
    have haux := (Boundary.CountReduction.Construction.boundaryAuxiliaryIdeal_prime_order_iff J L q m hm).mpr
      ⟨hJ, le_sup_right.trans hle⟩
    exact ((CompanionOrder.Construction.smooth_relative_terminal_iff_closed_power k _ m hm).mp hclear q) haux
  · intro hclear
    apply (CompanionOrder.Construction.smooth_relative_terminal_iff_closed_power k _ m hm).mpr
    intro q _ haux
    obtain ⟨hJ, hL⟩ := (Boundary.CountReduction.Construction.boundaryAuxiliaryIdeal_prime_order_iff J L q m hm).mp haux
    have hle := sup_le ((CompanionOrder.Construction.smooth_closedPoint_order_iff_differential_control k J q m hm).mp hJ) hL
    rw [hclear] at hle
    exact (inferInstance : q.IsMaximal).ne_top (top_le_iff.mp hle)

variable [Algebra ℚ R] {ι : Type u} [Fintype ι] [DecidableEq ι]

omit [CharZero k] in
/-- Every actual framed auxiliary center lies in the selected boundary
intersection and is permissible for the original marked ideal. -/
theorem smooth_generated_boundary_auxiliary_center_iff
    (I : Ideal R) (g : ι → I) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j).val = if i = j then 1 else 0)
    (hgen : Ideal.span (Set.range (fun i => (g i).val)) = I)
    (J L : Ideal R) (m : ℕ) (hm : 0 < m) :
    Boundary.AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal J L m ≤ I ^ m ↔ J ≤ I ^ m ∧ L ≤ I := by
  simpa only [Boundary.AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal, MarkedIdealIntersection.Construction.markedIdealIntersection, pow_one, Nat.mul_one] using
    MarkedIntersection.Construction.smooth_generated_center_markedIntersection_iff k I g D hD hgen J L m 1 hm Nat.zero_lt_one

end

/-- The terminal boundary identity excludes every prime of high local
residual order from the selected intersection, including nonclosed primes. -/
theorem boundary_auxiliary_clearance_at_every_prime (k : Type*) {R : Type*}
    [CommRing k] [CommRing R] [Algebra k R] (J L : Ideal R) (m : ℕ) (hm : 0 < m)
    (hclear : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (m - 1) ⊔ L = ⊤)
    (q : Ideal R) [q.IsPrime]
    (hJ : J.map (algebraMap R (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ m) : ¬ L ≤ q := by
  intro hL
  have hle := sup_le (ResidualDropAllPrimes.Construction.relative_differential_control_le_prime_of_local_order k J q m hm hJ) hL
  rw [hclear] at hle
  exact (inferInstance : q.IsPrime).ne_top (top_le_iff.mp hle)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.BoundaryAuxiliaryOrder.Construction
