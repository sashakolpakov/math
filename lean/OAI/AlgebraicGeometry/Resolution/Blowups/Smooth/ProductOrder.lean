import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ClosedPointChartTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.Ideal.ProductOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.MarkedIdealIntersection

/-! # Product Order -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ProductOrder.Construction

noncomputable section

/-! Exact product and strict power order on arbitrary smooth affine algebras. -/

variable (k : Type*) {R : Type*} [Field k] [IsAlgClosed k] [CommRing R]
  [Algebra k R] [Algebra.Smooth k R]

include k in
/-- On a closed-point stratum of exact order `m`, product order is exactly
the remaining factor's order, without global polynomial coordinates. -/
theorem smooth_closedPoint_product_order_iff (J M q : Ideal R) [q.IsMaximal]
    (m b : ℕ) (hmb : m ≤ b) (hJ : J ≤ q ^ m) (hJ1 : ¬ J ≤ q ^ (m + 1)) :
    M * J ≤ q ^ b ↔ M ≤ q ^ (b - m) := by
  obtain ⟨s, _, d, a, _, he, Q, hQ, hqQ⟩ := ClosedPointChartTransport.Construction.exists_smooth_closed_point_coordinate_chart k q
  let A := Localization.Away s
  let : Algebra (MvPolynomial (Fin d) k) A := a
  let : Algebra.Etale (MvPolynomial (Fin d) k) A := he
  let : Q.IsMaximal := hQ
  let f := algebraMap R A
  have hf : f.Etale := RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway s)
  have h (L : Ideal R) (r : ℕ) : L.map f ≤ Q ^ r ↔ L ≤ q ^ r :=
    ClosedPointChartTransport.Construction.etale_closedPoint_global_order_iff f hf L q Q hqQ r
  have hnew := Blowups.Ideal.ProductOrder.Construction.etale_closedPoint_product_order_iff (σ := Fin d) (K := k)
    (J.map f) (M.map f) Q m b hmb ((h J m).mpr hJ) (fun h' => hJ1 ((h J (m + 1)).mp h'))
  rw [← Ideal.map_mul] at hnew
  exact (h (M * J) b).symm.trans (hnew.trans (h M (b - m)))

include k in
/-- Strict order thresholds scale exactly under positive ideal powers on
any smooth affine algebra. -/
theorem smooth_closedPoint_power_strict_order_iff (J q : Ideal R) [q.IsMaximal]
    (m e : ℕ) (he : 0 < e) : J ^ e ≤ q ^ (m * e + 1) ↔ J ≤ q ^ (m + 1) := by
  obtain ⟨s, _, d, a, _, heA, Q, hQ, hqQ⟩ := ClosedPointChartTransport.Construction.exists_smooth_closed_point_coordinate_chart k q
  let A := Localization.Away s
  let : Algebra (MvPolynomial (Fin d) k) A := a
  let : Algebra.Etale (MvPolynomial (Fin d) k) A := heA
  let : Q.IsMaximal := hQ
  let f := algebraMap R A
  have hf : f.Etale := RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway s)
  have h (L : Ideal R) (r : ℕ) : L.map f ≤ Q ^ r ↔ L ≤ q ^ r :=
    ClosedPointChartTransport.Construction.etale_closedPoint_global_order_iff f hf L q Q hqQ r
  have hnew := MarkedIdealIntersection.Construction.etale_closedPoint_ideal_pow_strict_order_iff (σ := Fin d) (K := k)
    (J.map f) Q m e he
  rw [← Ideal.map_pow] at hnew
  exact (h (J ^ e) (m * e + 1)).symm.trans (hnew.trans (h J (m + 1)))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ProductOrder.Construction
