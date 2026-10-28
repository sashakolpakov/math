import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedWeightedOrder

/-! # Product Order -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Ideal.ProductOrder.Construction

noncomputable section

/-! Exact product order for arbitrary ideals in étale local coordinate rings. -/

variable {σ K S : Type*} [Field K] [IsAlgClosed K] [CommRing S] [Finite σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

/-- Exact finite orders add for arbitrary local ideals. -/
theorem etale_local_ideal_exact_order_mul
    (x : σ → K) (q : Ideal S) [q.IsMaximal] [q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x)]
    (J L : Ideal (Localization.AtPrime q)) (u v : ℕ)
    (hJ : J ≤ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ u)
    (hJ1 : ¬ J ≤ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (u + 1))
    (hL : L ≤ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ v)
    (hL1 : ¬ L ≤ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (v + 1)) :
    J * L ≤ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (u + v) ∧
      ¬ J * L ≤ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (u + v + 1) := by
  classical
  change ¬ ∀ s, s ∈ J → s ∈ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (u + 1) at hJ1
  change ¬ ∀ s, s ∈ L → s ∈ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (v + 1) at hL1
  push Not at hJ1 hL1
  obtain ⟨s, hs, hs1⟩ := hJ1
  obtain ⟨t, ht, ht1⟩ := hL1
  have hst := Blowups.Etale.MultiplicativeOrder.Construction.etale_local_exact_order_mul x q s t u v (hJ hs) hs1 (hL ht) ht1
  refine ⟨?_, fun h => hst.2 (h (Ideal.mul_mem_mul hs ht))⟩
  rw [pow_add]
  exact Ideal.mul_mono hJ hL

include σ K in
/-- The same exact product formula at every closed point of the affine algebra. -/
theorem etale_closedPoint_ideal_exact_order_mul (J L q : Ideal S) [q.IsMaximal] (u v : ℕ)
    (hJ : J ≤ q ^ u) (hJ1 : ¬ J ≤ q ^ (u + 1))
    (hL : L ≤ q ^ v) (hL1 : ¬ L ≤ q ^ (v + 1)) :
    J * L ≤ q ^ (u + v) ∧ ¬ J * L ≤ q ^ (u + v + 1) := by
  obtain ⟨x, hx⟩ := Blowups.Etale.ClosedOrder.Construction.finiteType_maximalIdeal_liesOver_polynomialPoint (K := K) (σ := σ) q
  let : q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x) := hx
  have hprod := etale_local_ideal_exact_order_mul x q
    (J.map (algebraMap S (Localization.AtPrime q))) (L.map (algebraMap S (Localization.AtPrime q))) u v
    ((ClosedWeightedOrder.Construction.closedPoint_local_order_iff J q u).mpr hJ)
    (fun h => hJ1 ((ClosedWeightedOrder.Construction.closedPoint_local_order_iff J q (u + 1)).mp h))
    ((ClosedWeightedOrder.Construction.closedPoint_local_order_iff L q v).mpr hL)
    (fun h => hL1 ((ClosedWeightedOrder.Construction.closedPoint_local_order_iff L q (v + 1)).mp h))
  simpa only [← Ideal.map_mul, ClosedWeightedOrder.Construction.closedPoint_local_order_iff] using hprod

include σ K in
omit [IsAlgClosed K] in
/-- Every ideal not vanishing in the local ring has finite exact order at
the closed point, even if the affine algebra is disconnected. -/
theorem etale_closedPoint_exists_ideal_order (J q : Ideal S) [q.IsMaximal]
    (hJ : J.map (algebraMap S (Localization.AtPrime q)) ≠ ⊥) :
    ∃ d : ℕ, J ≤ q ^ d ∧ ¬ J ≤ q ^ (d + 1) := by
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing (MvPolynomial σ K) S
  obtain ⟨d, hd, hd1⟩ := Order.Construction.exists_idealAdicOrder
    (IsLocalRing.maximalIdeal (Localization.AtPrime q)) (J.map (algebraMap S (Localization.AtPrime q)))
    (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime q)).ne_top hJ
  exact ⟨d, (ClosedWeightedOrder.Construction.closedPoint_local_order_iff J q d).mp hd,
    fun h => hd1 ((ClosedWeightedOrder.Construction.closedPoint_local_order_iff J q (d + 1)).mpr h)⟩

include σ K in
/-- On a stratum where the residual order is exactly `m`, the product's
order condition is precisely the remaining exceptional order condition. -/
theorem etale_closedPoint_product_order_iff (J M q : Ideal S) [q.IsMaximal]
    (m b : ℕ) (hmb : m ≤ b) (hJ : J ≤ q ^ m) (hJ1 : ¬ J ≤ q ^ (m + 1)) :
    M * J ≤ q ^ b ↔ M ≤ q ^ (b - m) := by
  constructor
  · intro hprod
    by_contra hM
    have hMlocal : M.map (algebraMap S (Localization.AtPrime q)) ≠ ⊥ := by
      intro hz
      apply hM
      apply (ClosedWeightedOrder.Construction.closedPoint_local_order_iff M q (b - m)).mp
      rw [hz]
      exact bot_le
    obtain ⟨d, hd, hd1⟩ := etale_closedPoint_exists_ideal_order (σ := σ) (K := K) M q hMlocal
    have hdm : d < b - m := by
      by_contra h
      exact hM (hd.trans (Ideal.pow_le_pow_right (by omega)))
    have hnot := (etale_closedPoint_ideal_exact_order_mul (σ := σ) (K := K) M J q d m hd hd1 hJ hJ1).2
    exact hnot (hprod.trans (Ideal.pow_le_pow_right (by omega : d + m + 1 ≤ b)))
  · intro hM
    have h := Ideal.mul_mono hM hJ
    rwa [← pow_add, Nat.sub_add_cancel hmb] at h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Ideal.ProductOrder.Construction
