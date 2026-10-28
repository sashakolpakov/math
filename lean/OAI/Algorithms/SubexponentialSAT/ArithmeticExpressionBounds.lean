import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# Size and time arithmetic for fixed expression programs

These natural-number bounds close the induction for the concrete arithmetic
expression compiler. They have no dependency on its syntax or semantics.
-/

namespace SubexponentialSAT.ArithmeticExpressionBounds

theorem width_bound {L a b wa wb : ℕ}
    (ha : wa ≤ a * (L + 1)) (hb : wb ≤ b * (L + 1)) :
    wa + wb + 1 ≤ (a + b + 1) * (L + 1) := by
  nlinarith

theorem binary_cost_bound {L a b wa wb ta tb taStep tbStep K : ℕ}
    (ha : wa ≤ a * (L + 1)) (hb : wb ≤ b * (L + 1))
    (hta : taStep ≤ ta * (L + 1)^2)
    (htb : tbStep ≤ tb * (L + 1)^2) :
    taStep + tbStep + 18 * L + 2 * wa + 2 * wb + 24 +
        K * (wa + wb + 1)^2 ≤
      (ta + tb + K * (a + b + 1)^2 + 100 * (a + b + 1)) * (L + 1)^2 := by
  have hN : L + 1 ≤ (L + 1)^2 := by nlinarith
  have hlinear : 18 * L + 2 * wa + 2 * wb + 24 ≤
      (2 * (a + b) + 42) * (L + 1) := by
    nlinarith only [ha, hb]
  have hcoeff : 2 * (a + b) + 42 ≤ 100 * (a + b + 1) := by omega
  have hover : 18 * L + 2 * wa + 2 * wb + 24 ≤
      (100 * (a + b + 1)) * (L + 1)^2 :=
    hlinear.trans (Nat.mul_le_mul hcoeff hN)
  have htime : taStep + tbStep ≤ (ta + tb) * (L + 1)^2 := by
    calc
      taStep + tbStep ≤ ta * (L + 1)^2 + tb * (L + 1)^2 :=
        Nat.add_le_add hta htb
      _ = (ta + tb) * (L + 1)^2 := by ring
  have hsquare : K * (wa + wb + 1)^2 ≤
      K * (a + b + 1)^2 * (L + 1)^2 := by
    calc
      K * (wa + wb + 1)^2 ≤ K * ((a + b + 1) * (L + 1))^2 :=
        Nat.mul_le_mul_left K (Nat.pow_le_pow_left (width_bound ha hb) 2)
      _ = K * (a + b + 1)^2 * (L + 1)^2 := by ring
  calc
    taStep + tbStep + 18 * L + 2 * wa + 2 * wb + 24 + K * (wa + wb + 1)^2 =
        (taStep + tbStep) + (18 * L + 2 * wa + 2 * wb + 24) +
          K * (wa + wb + 1)^2 := by ring
    _ ≤ (ta + tb) * (L + 1)^2 + (100 * (a + b + 1)) * (L + 1)^2 +
          K * (a + b + 1)^2 * (L + 1)^2 :=
      Nat.add_le_add (Nat.add_le_add htime hover) hsquare
    _ = (ta + tb + K * (a + b + 1)^2 + 100 * (a + b + 1)) * (L + 1)^2 := by
      ring

theorem unary_cost_bound {L a w t tStep : ℕ}
    (hw : w ≤ a * (L + 1)) (ht : tStep ≤ t * (L + 1)^2) :
    tStep + 9 * L + 29 * w + 40 ≤ (t + 100 * (a + 1)) * (L + 1)^2 := by
  have hN : L + 1 ≤ (L + 1)^2 := by nlinarith
  have hlinear : 9 * L + 29 * w + 40 ≤ (29 * a + 49) * (L + 1) := by
    nlinarith only [hw]
  have hcoeff : 29 * a + 49 ≤ 100 * (a + 1) := by omega
  have hover : 9 * L + 29 * w + 40 ≤ (100 * (a + 1)) * (L + 1)^2 :=
    hlinear.trans (Nat.mul_le_mul hcoeff hN)
  calc
    tStep + 9 * L + 29 * w + 40 = tStep + (9 * L + 29 * w + 40) := by ring
    _ ≤ t * (L + 1)^2 + (100 * (a + 1)) * (L + 1)^2 := Nat.add_le_add ht hover
    _ = (t + 100 * (a + 1)) * (L + 1)^2 := by ring

end SubexponentialSAT.ArithmeticExpressionBounds

end OAI.Algorithms
