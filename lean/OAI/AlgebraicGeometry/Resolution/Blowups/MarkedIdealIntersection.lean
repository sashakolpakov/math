import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedWeightedOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.ResidualCoefficientTransform

/-! # Marked Ideal Intersection -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.MarkedIdealIntersection.Construction

noncomputable section

section

/-! Intersections of marked ideal conditions, for the residual and exceptional factors. -/

variable {R : Type*} [CommRing R]

/-- The two controls `b` and `c` are combined at common control `b*c`. -/
def markedIdealIntersection (J L : Ideal R) (b c : ℕ) : Ideal R := J ^ c ⊔ L ^ b

theorem markedIdealIntersection_map {T : Type*} [CommRing T] (φ : R →+* T)
    (J L : Ideal R) (b c : ℕ) :
    (markedIdealIntersection J L b c).map φ = markedIdealIntersection (J.map φ) (L.map φ) b c := by
  simp only [markedIdealIntersection, Ideal.map_sup, Ideal.map_pow]

theorem markedIdealIntersection_permissible (I J L : Ideal R) (b c : ℕ)
    (hJ : J ≤ I ^ b) (hL : L ≤ I ^ c) :
    markedIdealIntersection J L b c ≤ I ^ (b * c) := by
  apply sup_le
  · simpa only [pow_mul] using pow_le_pow_left' hJ c
  · calc
      L ^ b ≤ (I ^ c) ^ b := pow_le_pow_left' hL b
      _ = I ^ (b * c) := by rw [← pow_mul, Nat.mul_comm c b]

/-- The two separate exceptional factors combine to the common control. -/
theorem markedIdealIntersection_factorization (t : R) (J L J' L' : Ideal R) (b c : ℕ)
    (hJ : J = Ideal.span {t ^ b} * J') (hL : L = Ideal.span {t ^ c} * L') :
    markedIdealIntersection J L b c = Ideal.span {t ^ (b * c)} *
      markedIdealIntersection J' L' b c := by
  simp only [markedIdealIntersection, hJ, hL, mul_pow, Ideal.span_singleton_pow,
    ← pow_mul, Nat.mul_comm c b, Ideal.mul_sup]

/-- The common controlled quotient equals the intersection of the two
separate controlled quotients. -/
theorem markedIdealIntersection_colon (t : R) (ht : IsRegular t)
    (J L : Ideal R) (b c : ℕ)
    (hJ : J ≤ Ideal.span {t ^ b}) (hL : L ≤ Ideal.span {t ^ c}) :
    (markedIdealIntersection J L b c).colon (Ideal.span {t ^ (b * c)}) =
      markedIdealIntersection (J.colon (Ideal.span {t ^ b})) (L.colon (Ideal.span {t ^ c})) b c := by
  rw [markedIdealIntersection_factorization t J L _ _ b c
    (ControlledTransform.Construction.principal_mul_colon_of_le J (t ^ b) hJ).symm (ControlledTransform.Construction.principal_mul_colon_of_le L (t ^ c) hL).symm]
  exact ResidualCoefficientTransform.Construction.colon_principal_mul_of_regular _ _ (ht.pow (b * c))

/-- This compatibility holds on the actual Rees charts of every permissible center. -/
theorem blowup_markedIdealIntersection_controlledTransform
    (I J L : Ideal R) (a : I) (b c : ℕ) (hJ : J ≤ I ^ b) (hL : L ≤ I ^ c) :
    ControlledTransform.Construction.blowupControlledTransform I (markedIdealIntersection J L b c) (b * c) a =
      markedIdealIntersection (ControlledTransform.Construction.blowupControlledTransform I J b a) (ControlledTransform.Construction.blowupControlledTransform I L c a) b c := by
  unfold ControlledTransform.Construction.blowupControlledTransform
  rw [markedIdealIntersection_map]
  exact markedIdealIntersection_colon _ (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a) _ _ b c
    (ControlledTransform.Construction.blowup_totalTransform_le_exceptionalPower I J b a hJ)
    (ControlledTransform.Construction.blowup_totalTransform_le_exceptionalPower I L c a hL)

variable {σ K S : Type*} [Field K] [IsAlgClosed K] [CommRing S] [Finite σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

include σ K in
theorem etale_closedPoint_ideal_pow_order_iff (J q : Ideal S) [q.IsMaximal]
    (b e : ℕ) (he : 0 < e) : J ^ e ≤ q ^ (b * e) ↔ J ≤ q ^ b := by
  obtain ⟨x, hx⟩ := Blowups.Etale.ClosedOrder.Construction.finiteType_maximalIdeal_liesOver_polynomialPoint (K := K) (σ := σ) q
  let : q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x) := hx
  simpa only [← Ideal.map_pow, ClosedWeightedOrder.Construction.closedPoint_local_order_iff] using
    Blowups.Etale.PowerOrder.Construction.etale_local_ideal_pow_le_pow_iff x q (J.map (algebraMap S (Localization.AtPrime q))) b e he

include σ K in
/-- The common ideal has exactly the intersection of the two high-order loci. -/
theorem etale_closedPoint_markedIdealIntersection_order_iff (J L q : Ideal S) [q.IsMaximal]
    (b c : ℕ) (hb : 0 < b) (hc : 0 < c) :
    markedIdealIntersection J L b c ≤ q ^ (b * c) ↔ J ≤ q ^ b ∧ L ≤ q ^ c := by
  rw [markedIdealIntersection, sup_le_iff,
    etale_closedPoint_ideal_pow_order_iff (σ := σ) (K := K) J q b c hc]
  conv_lhs => rhs; rw [Nat.mul_comm b c]
  rw [etale_closedPoint_ideal_pow_order_iff (σ := σ) (K := K) L q c b hb]

end

/-! Strict order thresholds under powers, used to control the companion ideal's maximum order. -/

variable {σ K S : Type*} [Field K] [IsAlgClosed K] [CommRing S] [Finite σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

/-- Order of a positive power exceeds `m*e` precisely when the original
section's order exceeds `m`. -/
theorem etale_local_pow_mem_strict_pow_iff
    (x : σ → K) (q : Ideal S) [q.IsMaximal] [q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x)]
    (s : Localization.AtPrime q) (m e : ℕ) (he : 0 < e) :
    s ^ e ∈ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (m * e + 1) ↔
      s ∈ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (m + 1) := by
  by_cases hs : s = 0
  · simp only [hs, zero_pow (Nat.ne_of_gt he), Submodule.zero_mem]
  · obtain ⟨d, hd, hd1⟩ := Blowups.Etale.PowerOrder.Construction.etale_local_exists_exact_order (σ := σ) (K := K) q s hs
    obtain ⟨hde, hde1⟩ := Blowups.Etale.PowerOrder.Construction.etale_local_exact_order_pow x q s d e hd hd1
    rw [Blowups.Etale.PowerOrder.Construction.ideal_mem_pow_iff_of_exact_order _ _ (d * e) (m * e + 1) hde hde1,
      Blowups.Etale.PowerOrder.Construction.ideal_mem_pow_iff_of_exact_order _ _ d (m + 1) hd hd1,
      ← Nat.lt_iff_add_one_le, ← Nat.lt_iff_add_one_le]
    exact Nat.mul_lt_mul_right he

theorem etale_local_ideal_pow_strict_order_iff
    (x : σ → K) (q : Ideal S) [q.IsMaximal] [q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x)]
    (J : Ideal (Localization.AtPrime q)) (m e : ℕ) (he : 0 < e) :
    J ^ e ≤ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (m * e + 1) ↔
      J ≤ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (m + 1) := by
  constructor
  · intro h s hs
    exact (etale_local_pow_mem_strict_pow_iff x q s m e he).mp (h (Ideal.pow_mem_pow hs e))
  · intro h
    have hpow := pow_le_pow_left' h e
    rw [← pow_mul] at hpow
    apply hpow.trans (Ideal.pow_le_pow_right _)
    rw [Nat.add_mul, Nat.one_mul]
    omega

include σ K in
theorem etale_closedPoint_ideal_pow_strict_order_iff (J q : Ideal S) [q.IsMaximal]
    (m e : ℕ) (he : 0 < e) : J ^ e ≤ q ^ (m * e + 1) ↔ J ≤ q ^ (m + 1) := by
  obtain ⟨x, hx⟩ := Blowups.Etale.ClosedOrder.Construction.finiteType_maximalIdeal_liesOver_polynomialPoint (K := K) (σ := σ) q
  let : q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x) := hx
  simpa only [← Ideal.map_pow, ClosedWeightedOrder.Construction.closedPoint_local_order_iff] using
    etale_local_ideal_pow_strict_order_iff x q (J.map (algebraMap S (Localization.AtPrime q))) m e he

include σ K in
/-- Exact finite ideal order multiplies under positive powers. -/
theorem etale_closedPoint_ideal_pow_exact_order (J q : Ideal S) [q.IsMaximal]
    (m e : ℕ) (he : 0 < e) (hJ : J ≤ q ^ m) (hJ1 : ¬ J ≤ q ^ (m + 1)) :
    J ^ e ≤ q ^ (m * e) ∧ ¬ J ^ e ≤ q ^ (m * e + 1) :=
  ⟨(etale_closedPoint_ideal_pow_order_iff (σ := σ) (K := K) J q m e he).mpr hJ,
    fun h => hJ1 ((etale_closedPoint_ideal_pow_strict_order_iff (σ := σ) (K := K) J q m e he).mp h)⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.MarkedIdealIntersection.Construction
