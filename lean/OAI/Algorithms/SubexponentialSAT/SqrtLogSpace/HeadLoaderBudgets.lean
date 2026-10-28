import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeTimeColumns

/-! Fixed polynomial bounds for the actual head loader from its retained
source words. Column time is derived from the native integer-entry program;
the outer loop's address is charged by its actual unary word length. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets

open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open SqrtLog.LeafHeadSetupProgram

/-- This constant is independent of the input and all runtime parameters. -/
def sizeCoefficient : ℕ := 10000000000000200

private theorem columnLength_polynomial (B X : ℕ) (hBX : B+2 ≤ X) :
    (B+1)*(100*(B+2)^2+2) ≤ 102*X^8 := by
  have hX : 1 ≤ X := by omega
  have hX2 : 1 ≤ X^2 := one_le_pow₀ hX
  have h38 : X^3 ≤ X^8 := pow_le_pow_right₀ hX (by decide)
  calc
    _ ≤ X*(100*X^2+2) := by gcongr; omega
    _ ≤ X*(102*X^2) := by gcongr; omega
    _ = 102*X^3 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ h38

/-- The source bank includes the ambient/factor counters, the complete row
word, low mask, native metadata and the integer-arithmetic widths. -/
theorem preparationSize_le (s : Native.Inputs) (a : Data) (B A z : ℕ)
    (ha : Native.Ready s a) (hB : WordBound B a)
    (hrows : s.rows.length = s.n+s.N) (hz : z ≤ A) :
    Bounds.preparationSize s.n s.N s.rows s.low (s.Q*s.r) z ≤ 7*B+A+2 := by
  have hn : s.n ≤ B := by simpa [ha.ambient,unary] using hB 128
  have hN : s.N ≤ B := by simpa [ha.factors,unary] using hB 129
  have hw : s.Q*s.r ≤ B := by simpa [ha.wordWidth,unary] using hB 132
  have hf : s.rows.flatten.length ≤ B := by simpa only [ha.words] using hB 133
  have hl : s.low.length ≤ B := by simpa only [ha.low] using hB 134
  unfold Bounds.preparationSize
  omega

/-- No column evaluator or successful running-time witness is assumed.
The actual native column budget follows from the physically stored inputs. -/
theorem workSize_le (s : Native.Inputs) (a : Data) (B A z : ℕ)
    (ha : Native.Ready s a) (hB : WordBound B a)
    (hrows : s.rows.length = s.n+s.N) (hz : z ≤ A) :
    SignatureHeadLoader.workSize s z A ≤ sizeCoefficient*(A+B+2)^8 := by
  let X := A+B+2
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hBX : B+2 ≤ X := by dsimp [X]; omega
  have hpow : X ≤ X^8 := by
    simpa only [pow_one] using pow_le_pow_right₀ hX (by decide : 1 ≤ 8)
  have h1 : 1 ≤ X^8 := one_le_pow₀ hX
  have hA : A ≤ X^8 := (show A ≤ X by dsimp [X]; omega).trans hpow
  have hBs : B ≤ X^8 := (show B ≤ X by dsimp [X]; omega).trans hpow
  have hi := NodeTime.inputBounds s a ha B hB
  have hc := NodeTime.columns_le hi
  have ht : s.columnTime ≤ 10000000000000000*X^8 :=
    hc.1.trans ((NodeTime.columnEnvelope_le (B+1)).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hBX 8)))
  have hl : s.columnLength ≤ 102*X^8 :=
    hc.2.trans (columnLength_polynomial B X hBX)
  have hp := preparationSize_le s a B A z ha hB hrows hz
  have hn := hi.n
  have hd := hi.D
  change SignatureHeadLoader.workSize s z A ≤ sizeCoefficient*X^8
  unfold SignatureHeadLoader.workSize sizeCoefficient
  omega

/-- The local native budget has a fixed degree, even when the outer scan
visits exponentially many assignments. It bounds each load independently. -/
theorem localWork_le (s : Native.Inputs) (a : Data) (B A z : ℕ)
    (ha : Native.Ready s a) (hB : WordBound B a)
    (hrows : s.rows.length = s.n+s.N) (hz : z ≤ A) :
    SignatureHeadLoader.localWork s z A ≤
      (100000000000000*sizeCoefficient^8)*(A+B+2)^64 := by
  apply (SignatureHeadLoader.localWork_le_monomial s z A).trans
  calc
    _ ≤ 100000000000000*(sizeCoefficient*(A+B+2)^8)^8 := by
      gcongr
      exact workSize_le s a B A z ha hB hrows hz
    _ = _ := by simp only [mul_pow, ← pow_mul, show 8*8=64 from rfl, mul_assoc]

/-- Paid address staging, import, export and cleanup have the same degree64
envelope. The resource use of the outer repeated run remains a separate bound. -/
theorem leafWork_le (s : Native.Inputs) (a : Data) (B A z : ℕ)
    (ha : Native.Ready s a) (hB : WordBound B a)
    (hrows : s.rows.length = s.n+s.N) (hz : z ≤ A) :
    36*A+22*(SignatureHeadLoader.localWork s z A+1)+35 ≤
      (10000000000000000*sizeCoefficient^8)*(A+B+2)^64 := by
  apply (SignatureHeadLoader.leafWork_le_monomial s z A).trans
  calc
    _ ≤ 10000000000000000*(sizeCoefficient*(A+B+2)^8)^8 := by
      gcongr
      exact workSize_le s a B A z ha hB hrows hz
    _ = _ := by simp only [mul_pow, ← pow_mul, show 8*8=64 from rfl, mul_assoc]


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets
