import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramNormalize
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSignatureBound

namespace OAI.Algorithms

/-! Exact integer meaning of the physical, canonical row keys. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

@[simp] theorem canonical_value (n : ℕ) :
    SubexponentialSAT.BinaryArithmetic.toNat (canonical n) = n := by
  apply SubexponentialSAT.SubexpLiftRing.toNat_fixedBits_of_lt
  simpa only [Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self Nat.one_lt_two n

theorem canonical_injective : Function.Injective canonical := by
  intro a b h
  have := congrArg SubexponentialSAT.BinaryArithmetic.toNat h
  simpa only [canonical_value] using this

theorem rowValue_ofFn {h : ℕ} (W : List Bool) (c : Fin h → List Bool) (x : Fin h → Bool) :
    rowValue W (List.ofFn c) (List.ofFn x) =
      ∑ i, if x i then SubexponentialSAT.BinaryArithmetic.toNat (c i) else SubexponentialSAT.BinaryArithmetic.toNat W := by
  have hz : List.zipWith (fun a b => if b then SubexponentialSAT.BinaryArithmetic.toNat a
      else SubexponentialSAT.BinaryArithmetic.toNat W) (List.ofFn c) (List.ofFn x) =
      List.ofFn (fun i => if x i then SubexponentialSAT.BinaryArithmetic.toNat (c i)
        else SubexponentialSAT.BinaryArithmetic.toNat W) := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp
  rw [rowValue, hz, List.sum_ofFn]

theorem rowValue_exact {h : ℕ} (W : List Bool) (c : Fin h → List Bool)
    (A : Fin h → ℤ) (x : Fin h → Bool)
    (hc : ∀ i, (SubexponentialSAT.BinaryArithmetic.toNat (c i) : ℤ) =
      (SubexponentialSAT.BinaryArithmetic.toNat W : ℤ) + A i) :
    (rowValue W (List.ofFn c) (List.ofFn x) : ℤ) =
      (h : ℤ)*(SubexponentialSAT.BinaryArithmetic.toNat W : ℤ) +
        ∑ i, A i*(if x i then 1 else 0) := by
  rw [rowValue_ofFn, Nat.cast_sum]
  have hs : (∑ i, ((if x i then SubexponentialSAT.BinaryArithmetic.toNat (c i)
        else SubexponentialSAT.BinaryArithmetic.toNat W) : ℕ) : ℤ) =
      offsetSignature (SubexponentialSAT.BinaryArithmetic.toNat W : ℤ) A x := by
    apply Finset.sum_congr rfl
    intro i hi
    cases hb : x i <;> simp [ hc]
  exact hs.trans (offsetSignature_eq _ _ _)

theorem rowKey_exact_iff {h : ℕ} (W : List Bool) (c : Fin h → List Bool)
    (A : Fin h → ℤ) (x y : Fin h → Bool)
    (hc : ∀ i, (SubexponentialSAT.BinaryArithmetic.toNat (c i) : ℤ) =
      (SubexponentialSAT.BinaryArithmetic.toNat W : ℤ)+A i) :
    canonical (1+rowValue W (List.ofFn c) (List.ofFn x)) =
      canonical (1+rowValue W (List.ofFn c) (List.ofFn y)) ↔
    (∑ i, A i*(if x i then 1 else 0)) = (∑ i, A i*(if y i then 1 else 0)) := by
  rw [canonical_injective.eq_iff, Nat.add_left_cancel_iff]
  have hx := rowValue_exact W c A x hc
  have hy := rowValue_exact W c A y hc
  constructor
  · intro hxy
    rw [hxy] at hx
    linarith
  · intro hxy
    have he : (rowValue W (List.ofFn c) (List.ofFn x) : ℤ) =
      rowValue W (List.ofFn c) (List.ofFn y) := by omega
    exact_mod_cast he

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
