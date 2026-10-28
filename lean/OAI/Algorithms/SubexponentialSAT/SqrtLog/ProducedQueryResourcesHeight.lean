import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResourcesConstructor

namespace OAI.Algorithms

/-! Bit width of the actual ambient-fiber coefficient-height envelope.
Its value need not be polynomial; only its binary width is placed among the
ordinary dimensions. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open LeafQueryFrontend Asymptotic

 theorem height_size (n B Q R : ℕ) (hn : 1 ≤ n)
    (hB : B ≤ n) (hQ : Q ≤ n) (hR : R ≤ n) :
    Nat.size (2*B*(8*Q)^(2*R)) ≤ 11*(n+1)^2 := by
  have hnexp : n ≤ 2^n := (show n < 2^n from Nat.lt_two_pow_self).le
  have hone : 2 ≤ 2^n := by simpa using Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) hn
  have htwoB : 2*B ≤ 2^(2*n) := by
    calc
      _ ≤ 2^n*2^n := Nat.mul_le_mul hone (hB.trans hnexp)
      _ = _ := by rw [←pow_add]; congr 1; omega
  have hbase : 8*Q ≤ 2^(4*n) := by
    calc
      _ ≤ 2^3*2^n := Nat.mul_le_mul_left 8 (hQ.trans hnexp)
      _ = 2^(3+n) := by rw [pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hpow : (8*Q)^(2*R) ≤ 2^(8*n^2) := by
    calc
      _ ≤ (2^(4*n))^(2*R) := Nat.pow_le_pow_left hbase _
      _ = 2^((4*n)*(2*R)) := (pow_mul _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith)
  have hval : 2*B*(8*Q)^(2*R) ≤ 2^(2*n+8*n^2) := by
    simpa only [pow_add] using Nat.mul_le_mul htwoB hpow
  have hsize : Nat.size (2*B*(8*Q)^(2*R)) ≤ 2*n+8*n^2+1 := by
    apply Nat.size_le.mpr
    exact hval.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  exact hsize.trans (by nlinarith)

 theorem matrixHeight_size (q : Query) (k n : ℕ) (hv : q.Valid)
    (hqn : ambient q=n) (hs : SmallInputs q k n)
    (hg : LeafParametersProgram.Guard (q.input k)) :
    Nat.size (matrixHeight q k) ≤ 11*(n+1)^2 := by
  have hn : 1 ≤ n := by
    have hpos : 0 < ambient q := hv.2.1
    omega
  have hqb := hg.2.2.2.2.2.2.1
  have hrb := hg.2.2.2.2.2.2.2.1
  have hbudget := hg.2.2.2.2.2.2.2.2.2
  have hr := layoutR_ge_two (q.input k).freeCount
  change 2 ≤ layoutQ (q.input k).freeCount at hqb
  change 4*layoutCutoff (q.input k).freeCount (q.input k).occurrence ≤ layoutQ (q.input k).freeCount at hrb
  change 16*layoutQ (q.input k).freeCount*(layoutR (q.input k).freeCount)^2 ≤ (q.input k).freeCount at hbudget
  have hQ : layoutQ (q.input k).freeCount ≤ n := by
    have hp : 1 ≤ (layoutR (q.input k).freeCount)^2 := Nat.one_le_pow _ _ (by omega)
    have hh : layoutQ (q.input k).freeCount ≤
        16*layoutQ (q.input k).freeCount*(layoutR (q.input k).freeCount)^2 :=
      (show layoutQ (q.input k).freeCount ≤ 16*layoutQ (q.input k).freeCount by omega).trans
        (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (16*layoutQ (q.input k).freeCount) hp)
    exact hh.trans (hbudget.trans hs.free)
  have hR : layoutCutoff (q.input k).freeCount (q.input k).occurrence ≤ n := by omega
  exact height_size n _ _ _ hn hs.occurrence hQ hR

end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
