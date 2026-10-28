import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutCoefficientBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutPackingBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutCacheBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutRowBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainLocalBasisBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutSizes

namespace OAI.Algorithms

/-! Common polynomial majorants for the measured layout stages. -/

namespace SubexponentialSAT.SubexpMainLayoutMajorants

open SubexpMainProgram SubexpMainLayoutWordBounds
open SubexpLayoutPorts (Allocation)

def coefficientConstant : ℕ := 22000001000 * 70^7
def cacheConstant : ℕ := SubexpMainLayoutCacheArithmetic.polynomialConstant *
  2^SubexpMainLayoutCacheArithmetic.polynomialDegree
def rowConstant (k : ℕ) : ℕ := 10^40 * (4*k+15)^13

theorem coefficient_bound (W X p Q R : ℕ) [Fact p.Prime]
    (hp : p ≤ X) (hQ : Q ≤ X) (hR : R ≤ X)
    (hpower : p^R ≤ X) :
    SubexpMainLayoutCoefficientBounds.bound W p Q R ≤
      coefficientConstant * (W+X+1)^8 := by
  have hw : Subexp.MatrixWordEncoding.width p ≤ X+1 := by
    simpa only [Subexp.MatrixWordEncoding.width, SubexpLiftRing.baseWidth, one_mul] using
      Nat.add_le_add_right ((Nat.log_le_self 2 p).trans hp) 1
  have hs : 64*W+p+Q+R+Subexp.MatrixWordEncoding.width p+2 ≤ 70*(W+X+1) := by omega
  calc
    _ ≤ 22000001000 * (64*W+p+Q+R+Subexp.MatrixWordEncoding.width p+2)^7 * p^R :=
      SubexpMainLayoutCoefficientBounds.bound_le_polynomial_times_power W p Q R
    _ ≤ 22000001000 * (70*(W+X+1))^7 * (W+X+1) := by gcongr; omega
    _ = coefficientConstant * (W+X+1)^8 := by unfold coefficientConstant; ring

theorem packing_bound (W X : ℕ) :
    SubexpMainLayoutPackingBounds.packingCoefficient * (W+1)^12 ≤
      SubexpMainLayoutPackingBounds.packingCoefficient * (W+X+1)^12 := by gcongr; omega

private theorem scale_two (C d W X p D : ℕ) (hp : p ≤ X) (hD : D ≤ X) :
    C*(W+p+D+2)^d ≤ (C*2^d)*(W+X+1)^d := by
  have hs : W+p+D+2 ≤ 2*(W+X+1) := by omega
  calc
    _ ≤ C*(2*(W+X+1))^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hs d)
    _ = _ := by rw [mul_pow]; exact (Nat.mul_assoc _ _ _).symm

theorem cache_bound (W X p D : ℕ) (hp : p ≤ X) (hD : D ≤ X) :
    SubexpMainLayoutCacheArithmetic.polynomialConstant *
        (W+p+D+2)^SubexpMainLayoutCacheArithmetic.polynomialDegree ≤
      cacheConstant * (W+X+1)^SubexpMainLayoutCacheArithmetic.polynomialDegree :=
  scale_two _ _ W X p D hp hD

theorem local_bound {er es W X p r Q Δ : ℕ} [Fact p.Prime]
    (alloc : Allocation es) (hregs : 16 ≤ er) (a : MainState er es)
    (hr : 0 < r) (hQ : 0 < Q) (coefficients alphabet : List (ZMod p))
    (hW : RelevantWordBound W a)
    (hcounter : CounterPrograms.value (a.stacks (persistent es 25)) = coefficients.length)
    (hR : coefficients.length ≤ X) (hrX : r ≤ X) (hQX : Q ≤ X)
    (hnative : Subexp.LocalBasisBatchProgram.sourceBudget (Δ := Δ) p hr hQ coefficients alphabet ≤ X) :
    SubexpMainLocalBasis.executionBound (Δ := Δ) alloc hregs a p hr hQ coefficients alphabet ≤
      200 * (W+X+1)^2 := by
  have hb := parameter hW (25 : Fin 32)
    (by norm_num [SubexpMainInvariant.ParameterPort, Fin.coe_ofNat_eq_mod])
  have h111 := ordinary hW alloc (111 : Fin 672)
  have h654 := ordinary hW alloc (654 : Fin 672)
  change (a.stacks (SubexpLayoutPorts.master alloc 14)).length ≤ W at h654
  rw [SubexpMainLocalBasis.executionBound_eq alloc hregs a p hr hQ coefficients alphabet hcounter]
  have hm : (coefficients.length+1)*((a.stacks (persistent es 25)).length+1) ≤ (W+X+1)^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hqr : Q*r ≤ (W+X+1)^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hsq : W+X+1 ≤ (W+X+1)^2 := Nat.le_self_pow (by decide) _
  nlinarith only [hm, hqr, hsq, hnative, hb, h111, h654, hR,
    Nat.zero_le W, Nat.zero_le X]

theorem scope_bound {er es n k T X : ℕ} {alloc : Allocation es}
    {a : MainState er es} {G : SubexpLeafData.Leaf n}
    (input : SubexpMainLayoutInput.Ready alloc a n k T G) (hk : 1 ≤ k)
    (hD : SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a) ≤ X)
    (hδ : DyadicSchedule.delta k T n ≤ X) :
    (SubexpDenseRowTableProgram.scopesCode (SubexpMainScheduledLayout.scopes input)).length ≤
      (4*k+5)*(X+1)^3 := by
  have hm := SubexpMainLayoutSizes.scope_count input hk
  have hbytes := SubexpMainLayoutSizes.scope_bytes input hk
  have hmX : (SubexpMainScheduledLayout.scopes input).length ≤ X^2 := by
    exact hm.trans (by simpa only [pow_two] using Nat.mul_le_mul hδ hD)
  change (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
    (SubexpMainScheduledLayout.scopes input)).length ≤ _
  calc
    _ ≤ 1+(2*(1+(2*X+2)*k)+2)*X^2 := by apply hbytes.trans; gcongr
    _ ≤ (4*k+5)*(X+1)^3 := by ring_nf; omega

theorem row_scale_bound (W X p r Q Δ D R N k : ℕ)
    (hp : p ≤ X) (hr : r ≤ X) (hQ : Q ≤ X) (hδ : Δ ≤ X) (hD : D ≤ X) (hR : R ≤ X)
    (hN : N ≤ (4*k+5)*(X+1)^3) :
    SubexpMainLayoutRowBounds.scale p r Q Δ D (D+1) R N W ≤
      (4*k+15)*(W+X+1)^3 := by
  let Y := W+X+1
  have hY : 1 ≤ Y := by dsimp [Y]; omega
  have hXY : X+1 ≤ Y := by dsimp [Y]; omega
  have hWY : W ≤ Y := by dsimp [Y]; omega
  have hpow : Y ≤ Y^3 := Nat.le_self_pow (by decide) Y
  have hpow2 : Y^2 ≤ Y^3 := Nat.pow_le_pow_right hY (by decide)
  have hb : SubexpLiftRing.baseWidth p 1 ≤ Y^3 := by
    have hw : SubexpLiftRing.baseWidth p 1 ≤ X+1 := by
      simpa only [SubexpLiftRing.baseWidth, one_mul] using
        Nat.add_le_add_right ((Nat.log_le_self 2 p).trans hp) 1
    exact hw.trans (hXY.trans hpow)
  have hB : SubexpLiftRing.baseWidth p (D+1) ≤ Y^3 := by
    have := SubexpMainCacheBounds.baseWidth_le_square hp hD
    exact this.trans ((Nat.pow_le_pow_left hXY 2).trans hpow2)
  have ht : Subexp.CollisionProgram.typeWidth r Q Δ ≤ Y^3 := by
    unfold Subexp.CollisionProgram.typeWidth
    calc
      _ ≤ (Y*Y)*Y := Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      _ = Y^3 := by ring
  have hN' : N ≤ (4*k+5)*Y^3 := hN.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hXY 3))
  have hother : W+r+Q+Δ+D+R+1 ≤ 7*Y^3 := by nlinarith only [hpow, hWY, hr, hQ, hδ, hD, hR, hXY]
  unfold SubexpMainLayoutRowBounds.scale
  change _ ≤ (4*k+15)*Y^3
  nlinarith only [hb, hB, ht, hN', hother]

theorem row_bound (W X p r Q Δ D R N k : ℕ)
    (hp : p ≤ X) (hr : r ≤ X) (hQ : Q ≤ X) (hδ : Δ ≤ X) (hD : D ≤ X) (hR : R ≤ X)
    (hN : N ≤ (4*k+5)*(X+1)^3) :
    SubexpMainLayoutRowBounds.polynomial
        (SubexpMainLayoutRowBounds.scale p r Q Δ D (D+1) R N W) ≤
      rowConstant k * (W+X+1)^39 := by
  unfold SubexpMainLayoutRowBounds.polynomial
  calc
    _ ≤ 10^40*((4*k+15)*(W+X+1)^3)^13 := by
      gcongr
      exact row_scale_bound W X p r Q Δ D R N k hp hr hQ hδ hD hR hN
    _ = _ := by unfold rowConstant; rw [mul_pow, ← pow_mul]; exact (Nat.mul_assoc _ _ _).symm

end SubexponentialSAT.SubexpMainLayoutMajorants

end OAI.Algorithms
