import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-! A pure arithmetic normalization of the actual dense-product byte budget.
The bridge to the executable program's budget is kept in
SubexpDenseProductBounds so this lemma can be checked independently of the
machine-program dependency chain. -/

namespace SubexponentialSAT.SubexpDenseArithmetic

def formula (B I P Q S : ℕ) : ℕ :=
  let record := 4 * I + 16 * B + 6
  let pair := 400000 * (B + 1)^2 + 80 * I + 280 * B + 150
  let scan := 30 * I + 4 * (6000 * (B + 1)^2 + 31 * B + 25) + 220 * B + 180
  let leftBits := 1 + record * P
  let rightBits := 1 + record * Q
  let pairBits := 1 + record * (P * Q)
  2 + (7 * leftBits + 5 +
    (3 + P * ((3 + Q * (pair + 12 * I + 48 * B + 19)) +
      7 * rightBits + 20 * I + 70 * B + 50 + 12 * I + 48 * B + 19))) +
    (4 + S * (6 * I + scan * (pairBits + 1) + 7)) + 2 * pairBits + 4

theorem formula_mono (B I P Q S N : ℕ) (hP : P ≤ N) (hQ : Q ≤ N) (hS : S ≤ N) :
    formula B I P Q S ≤ formula B I N N N := by
  dsimp [formula]
  gcongr

theorem formula_le (B I P Q S N : ℕ) (hP : P ≤ N) (hQ : Q ≤ N) (hS : S ≤ N) :
    formula B I P Q S ≤ 2000000 * (B + I + 1)^3 * (N + 1)^3 := by
  apply (formula_mono B I P Q S N hP hQ hS).trans
  unfold formula
  ring_nf
  omega

end SubexponentialSAT.SubexpDenseArithmetic

end OAI.Algorithms
