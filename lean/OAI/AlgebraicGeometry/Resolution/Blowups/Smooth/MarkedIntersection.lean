import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DualCenterPowerRoot
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ClosedPointPowerRoot
import OAI.AlgebraicGeometry.Resolution.Blowups.CompanionCenter

/-! # Marked Intersection -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.MarkedIntersection.Construction

noncomputable section

/-! Exact marked-intersection and companion conditions along arbitrary actual dual-frame centers. -/

universe u

variable (k : Type u) {R : Type u} [Field k] [IsAlgClosed k] [CommRing R]
  [Algebra k R] [Algebra.Smooth k R]

include k in
theorem smooth_closedPoint_power_order_iff (J q : Ideal R) [q.IsMaximal]
    (b e : ℕ) (he : 0 < e) : J ^ e ≤ q ^ (b * e) ↔ J ≤ q ^ b := by
  constructor
  · exact ClosedPointPowerRoot.Construction.smooth_closedPoint_ideal_power_root k J q b e he
  · intro h
    simpa only [pow_mul] using pow_le_pow_left' h e

include k in
/-- A marked intersection encodes exactly the intersection of the original
closed-point order conditions on any smooth affine algebra. -/
theorem smooth_closedPoint_markedIntersection_order_iff (J L q : Ideal R) [q.IsMaximal]
    (b c : ℕ) (hb : 0 < b) (hc : 0 < c) :
    MarkedIdealIntersection.Construction.markedIdealIntersection J L b c ≤ q ^ (b * c) ↔ J ≤ q ^ b ∧ L ≤ q ^ c := by
  rw [MarkedIdealIntersection.Construction.markedIdealIntersection, sup_le_iff, smooth_closedPoint_power_order_iff k J q b c hc]
  conv_lhs => rhs; rw [Nat.mul_comm b c]
  rw [smooth_closedPoint_power_order_iff k L q c b hb]

variable [Algebra ℚ R] {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Actual finite dual generators of a center recover both separate
permissibility conditions from their common marked-intersection control. -/
theorem smooth_generated_center_markedIntersection_iff
    (I : Ideal R) (g : ι → I) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j).val = if i = j then 1 else 0)
    (hgen : Ideal.span (Set.range (fun i => (g i).val)) = I)
    (J L : Ideal R) (b c : ℕ) (hb : 0 < b) (hc : 0 < c) :
    MarkedIdealIntersection.Construction.markedIdealIntersection J L b c ≤ I ^ (b * c) ↔ J ≤ I ^ b ∧ L ≤ I ^ c := by
  constructor
  · intro h
    have hJ : J ^ c ≤ (Ideal.span (Set.range (fun i => (g i).val))) ^ (b * c) := by
      rw [hgen]
      exact le_sup_left.trans h
    have hL : L ^ b ≤ (Ideal.span (Set.range (fun i => (g i).val))) ^ (c * b) := by
      rw [hgen, Nat.mul_comm c b]
      exact le_sup_right.trans h
    have hJ' := DualCenterPowerRoot.Construction.smooth_dual_center_ideal_power_root k (fun i => (g i).val) D hD J b c hc hJ
    have hL' := DualCenterPowerRoot.Construction.smooth_dual_center_ideal_power_root k (fun i => (g i).val) D hD L c b hb hL
    simpa only [hgen] using And.intro hJ' hL'
  · rintro ⟨hJ, hL⟩
    exact MarkedIdealIntersection.Construction.markedIdealIntersection_permissible I J L b c hJ hL

/-- A companion-permissible actual dual-frame center is permissible for
both separately controlled factors and for the original product control. -/
theorem smooth_generated_companion_center_permissible
    (I : Ideal R) (g : ι → I) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j).val = if i = j then 1 else 0)
    (hgen : Ideal.span (Set.range (fun i => (g i).val)) = I)
    (J M : Ideal R) (m b : ℕ) (hm : 0 < m) (hmb : m < b)
    (hcomp : CompanionCenter.Construction.companionIdeal J M m b ≤ I ^ (m * (b - m))) :
    J ≤ I ^ m ∧ M ≤ I ^ (b - m) ∧ M * J ≤ I ^ b := by
  obtain ⟨hJ, hM⟩ := (smooth_generated_center_markedIntersection_iff k I g D hD hgen
    J M m (b - m) hm (by omega)).mp hcomp
  exact ⟨hJ, hM, ResidualCoefficientTransform.Construction.product_center_permissible I M J (b - m) m b (by omega) hM hJ⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.MarkedIntersection.Construction
