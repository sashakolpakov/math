import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchCost

namespace OAI.Algorithms

/-!
# A coarse bound for the concrete local basis-search cost

The expression below is the displayed bound for tuple preparation and the
three nested search loops. A separate adapter identifies it with the actual
program's proved cost; this module only performs the numerical absorption.
-/

namespace SubexponentialSAT.Subexp.BlockSearchArithmetic

def coefficientExpression (m N B : ℕ) : ℕ :=
  200000 * (m + 1) * (N + 1) ^ 2 * (B + 1) ^ 2

def searchExpression (p N W A : ℕ) : ℕ :=
  p ^ (N * N) * ((N + 1) * (p ^ N * (24 * (N * W) + A + 27) +
    35 * N + 62) + 15 * (N * N * W) + 41) + 9

def costExpression (p m N B : ℕ) : ℕ :=
  800 * (N * N + 1) * p ^ (N * N) * ((N * N + 1) * (2 * B + 1) + 1) +
  800 * (N + 1) * p ^ N * ((N + 1) * (2 * B + 1) + 1) +
  6 * N ^ 2 + 22 * N + 37 +
  searchExpression p N (2 * B + 1) (coefficientExpression m N B)

theorem costExpression_le (p m N B : ℕ) (hp : 1 ≤ p)
    (hm : m ≤ N ^ 2) (hB : B ≤ N) :
    costExpression p m N B ≤ 1000000 * (N + 1) ^ 8 * p ^ (N * N + N) := by
  let X := N + 1
  let Q := p ^ (N * N + N)
  let G := X ^ 8 * Q
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hNX : N ≤ X := by dsimp [X]; omega
  have hpN : 1 ≤ p ^ N := by simpa using Nat.pow_le_pow_left hp N
  have hpNN : 1 ≤ p ^ (N * N) := by simpa using Nat.pow_le_pow_left hp (N * N)
  have hQ : 1 ≤ Q := by simpa [Q] using Nat.pow_le_pow_left hp (N * N + N)
  have hprod : p ^ (N * N) * p ^ N = Q := by simp only [Q, pow_add]
  have hNQ : p ^ N ≤ Q := Nat.pow_le_pow_right hp (by omega)
  have hNNQ : p ^ (N * N) ≤ Q := Nat.pow_le_pow_right hp (by omega)
  have hpow (a b : ℕ) (h : a ≤ b) : X ^ a ≤ X ^ b := Nat.pow_le_pow_right hX h
  have hXpow (a : ℕ) (h : 1 ≤ a) : X ≤ X ^ a := by simpa using hpow 1 a h
  have hone (a : ℕ) : 1 ≤ X ^ a := by simpa using Nat.pow_le_pow_left hX a
  have hG : 1 ≤ G := by simpa [G] using Nat.mul_le_mul (hone 8) hQ
  have hW : 2 * B + 1 ≤ 2 * X := by dsimp [X]; omega
  have hB1 : B + 1 ≤ X := by dsimp [X]; omega
  have hN2 : N * N + 1 ≤ X ^ 2 := by dsimp [X]; nlinarith
  have hm1 : m + 1 ≤ X ^ 2 := by dsimp [X]; nlinarith
  have hA : coefficientExpression m N B ≤ 200000 * X ^ 6 := by
    calc
      _ ≤ 200000 * X ^ 2 * X ^ 2 * X ^ 2 := by
        unfold coefficientExpression
        exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hm1))
          (Nat.pow_le_pow_left hB1 2)
      _ = _ := by ring
  have hNW : N * (2 * B + 1) ≤ 2 * X ^ 2 := by
    calc
      _ ≤ X * (2 * X) := Nat.mul_le_mul hNX hW
      _ = _ := by ring
  have hNNW : N * N * (2 * B + 1) ≤ 2 * X ^ 3 := by
    calc
      _ ≤ (X * X) * (2 * X) := Nat.mul_le_mul (Nat.mul_le_mul hNX hNX) hW
      _ = _ := by ring
  have hb1 : (N * N + 1) * (2 * B + 1) + 1 ≤ 3 * X ^ 3 := by
    have hmul : (N * N + 1) * (2 * B + 1) ≤ 2 * X ^ 3 := by
      calc
        _ ≤ X ^ 2 * (2 * X) := Nat.mul_le_mul hN2 hW
        _ = _ := by ring
    have := hone 3
    omega
  have ht1 : 800 * (N * N + 1) * p ^ (N * N) *
      ((N * N + 1) * (2 * B + 1) + 1) ≤ 2400 * G := by
    calc
      _ ≤ 800 * X ^ 2 * Q * (3 * X ^ 3) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hN2) hNNQ) hb1
      _ = 2400 * X ^ 5 * Q := by ring
      _ ≤ 2400 * X ^ 8 * Q := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hpow 5 8 (by decide)))
      _ = _ := by dsimp [G]; ring
  have hb2 : (N + 1) * (2 * B + 1) + 1 ≤ 3 * X ^ 2 := by
    have hmul : (N + 1) * (2 * B + 1) ≤ 2 * X ^ 2 := by
      calc
        _ ≤ X * (2 * X) := Nat.mul_le_mul_left _ hW
        _ = _ := by ring
    have := hone 2
    omega
  have ht2 : 800 * (N + 1) * p ^ N * ((N + 1) * (2 * B + 1) + 1) ≤ 2400 * G := by
    calc
      _ ≤ 800 * X * Q * (3 * X ^ 2) := Nat.mul_le_mul
        (Nat.mul_le_mul_left (800 * X) hNQ) hb2
      _ = 2400 * X ^ 3 * Q := by ring
      _ ≤ 2400 * X ^ 8 * Q := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hpow 3 8 (by decide)))
      _ = _ := by dsimp [G]; ring
  have hlinear : 6 * N ^ 2 + 22 * N + 37 ≤ 100 * G := by
    have hbase : 6 * N ^ 2 + 22 * N + 37 ≤ 100 * X ^ 2 := by dsimp [X]; nlinarith
    have h8 : X ^ 2 ≤ X ^ 8 := hpow 2 8 (by decide)
    have hmul : X ^ 8 ≤ G := by simpa [G] using Nat.mul_le_mul_left (X ^ 8) hQ
    exact hbase.trans (Nat.mul_le_mul_left _ (h8.trans hmul))
  have hcore : 24 * (N * (2 * B + 1)) + coefficientExpression m N B + 27 ≤ 200100 * X ^ 6 := by
    have h26 := hpow 2 6 (by decide)
    have h16 := hone 6
    omega
  have hsmall : 35 * N + 62 ≤ 100 * X ^ 6 := by
    have hx6 := hXpow 6 (by decide)
    have h16 := hone 6
    omega
  have hinner : p ^ N * (24 * (N * (2 * B + 1)) + coefficientExpression m N B + 27) +
      35 * N + 62 ≤ 200200 * X ^ 6 * p ^ N := by
    have hc := Nat.mul_le_mul_left (p ^ N) hcore
    have hs := hsmall.trans (by
      simpa using Nat.mul_le_mul_left (100 * X ^ 6) hpN)
    nlinarith
  have hextra : 15 * (N * N * (2 * B + 1)) + 41 ≤ 100 * X ^ 7 * p ^ N := by
    have h37 := hpow 3 7 (by decide)
    have h17 := hone 7
    have hbase : 15 * (N * N * (2 * B + 1)) + 41 ≤ 100 * X ^ 7 := by omega
    exact hbase.trans (by simpa using Nat.mul_le_mul_left (100 * X ^ 7) hpN)
  have hbody : (N + 1) *
      (p ^ N * (24 * (N * (2 * B + 1)) + coefficientExpression m N B + 27) + 35 * N + 62) +
      15 * (N * N * (2 * B + 1)) + 41 ≤ 200300 * X ^ 7 * p ^ N := by
    have hi : (N + 1) *
        (p ^ N * (24 * (N * (2 * B + 1)) + coefficientExpression m N B + 27) + 35 * N + 62) ≤
          200200 * X ^ 7 * p ^ N := by
      calc
        _ ≤ X * (200200 * X ^ 6 * p ^ N) := Nat.mul_le_mul_left X hinner
        _ = _ := by ring
    nlinarith only [hi, hextra]
  have hsearch : searchExpression p N (2 * B + 1) (coefficientExpression m N B) ≤ 200400 * G := by
    have hm : p ^ (N * N) * ((N + 1) *
        (p ^ N * (24 * (N * (2 * B + 1)) + coefficientExpression m N B + 27) + 35 * N + 62) +
        15 * (N * N * (2 * B + 1)) + 41) ≤ 200300 * G := by
      calc
        _ ≤ p ^ (N * N) * (200300 * X ^ 7 * p ^ N) := Nat.mul_le_mul_left _ hbody
        _ = 200300 * X ^ 7 * Q := by rw [← hprod]; ring
        _ ≤ 200300 * X ^ 8 * Q := Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left _ (hpow 7 8 (by decide)))
        _ = _ := by dsimp [G]; ring
    have hnine : 9 ≤ 100 * G := by nlinarith
    unfold searchExpression
    calc
      _ ≤ 200300 * G + 9 := Nat.add_le_add_right hm 9
      _ ≤ 200300 * G + 100 * G := Nat.add_le_add_left hnine _
      _ = 200400 * G := by ring
  change _ ≤ 1000000 * X ^ 8 * Q
  have hfinal : costExpression p m N B ≤ 1000000 * G := by
    rw [show costExpression p m N B =
        (800 * (N * N + 1) * p ^ (N * N) * ((N * N + 1) * (2 * B + 1) + 1)) +
        (800 * (N + 1) * p ^ N * ((N + 1) * (2 * B + 1) + 1)) +
        (6 * N ^ 2 + 22 * N + 37) +
        searchExpression p N (2 * B + 1) (coefficientExpression m N B) by
      unfold costExpression
      ring]
    calc
      _ ≤ 2400 * G + 2400 * G + 100 * G + 200400 * G :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ht1 ht2) hlinear) hsearch
      _ ≤ 1000000 * G := by omega
  simpa only [G, Nat.mul_assoc] using hfinal

theorem polynomial_times_search_le_two_pow (p N : ℕ) (hpN : p ≤ N) :
    1000000 * (N + 1) ^ 8 * p ^ (N * N + N) ≤
      2 ^ (1000000 * (N + 1) ^ 10) := by
  let X := N + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hNX : N ≤ X := by dsimp [X]; omega
  have hXtwo : X ≤ 2 ^ X := le_of_lt Nat.lt_two_pow_self
  have hptwo : p ≤ 2 ^ X := hpN.trans (hNX.trans hXtwo)
  have hc : 1000000 ≤ 2 ^ 20 := by decide
  have hpow (a b : ℕ) (h : a ≤ b) : X ^ a ≤ X ^ b := Nat.pow_le_pow_right hX h
  have hN2 : N * N ≤ X ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hNX hNX
  have hX2 : X ≤ X ^ 2 := by simpa using hpow 1 2 (by decide)
  have hsum : N * N + N ≤ 2 * X ^ 2 := by omega
  have hproduct : X * (N * N + N) ≤ 2 * X ^ 3 := by
    calc
      _ ≤ X * (2 * X ^ 2) := Nat.mul_le_mul_left X hsum
      _ = _ := by ring
  have hx10 : X ≤ X ^ 10 := by simpa using hpow 1 10 (by decide)
  have h310 := hpow 3 10 (by decide)
  have h110 : 1 ≤ X ^ 10 := by simpa using Nat.pow_le_pow_left hX 10
  have hexp : 20 + X * 8 + X * (N * N + N) ≤ 1000000 * X ^ 10 := by omega
  change 1000000 * X ^ 8 * p ^ (N * N + N) ≤ _
  calc
    _ ≤ 2 ^ 20 * (2 ^ X) ^ 8 * (2 ^ X) ^ (N * N + N) :=
      Nat.mul_le_mul (Nat.mul_le_mul hc (Nat.pow_le_pow_left hXtwo 8))
        (Nat.pow_le_pow_left hptwo (N * N + N))
    _ = 2 ^ (20 + X * 8 + X * (N * N + N)) := by simp only [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (1000000 * X ^ 10) := Nat.pow_le_pow_right (by decide) hexp

theorem costExpression_le_two_pow (p m N B : ℕ) (hp : 1 ≤ p)
    (hpN : p ≤ N) (hm : m ≤ N ^ 2) (hB : B ≤ N) :
    costExpression p m N B ≤ 2 ^ (1000000 * (N + 1) ^ 10) :=
  (costExpression_le p m N B hp hm hB).trans (polynomial_times_search_le_two_pow p N hpN)

end SubexponentialSAT.Subexp.BlockSearchArithmetic

end OAI.Algorithms
