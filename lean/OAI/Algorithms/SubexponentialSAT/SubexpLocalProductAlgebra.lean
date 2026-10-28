import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl
import OAI.Algorithms.SubexponentialSAT.SubexpLocalCorrectionAlgebra

namespace OAI.Algorithms

/-! The exact value schedule of the physical node/power loops gives the
same local cofactor as the general-ring CRT reconstruction theorem. -/

namespace SubexponentialSAT.SubexpLocalProductAlgebra

open Polynomial
open scoped BigOperators

theorem repeatProduct_eq_iterate {S : Type*} (mul : S → S → S)
    (factor : S) (n : ℕ) (a : S) :
    SubexpLocalCorrectionAlgebra.repeatProduct mul factor n a =
      ((fun x => mul x factor)^[n]) a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
      rw [SubexpLocalCorrectionAlgebra.repeatProduct, ih, Function.iterate_succ_apply]

theorem localProduct_eq_foldl {S C : Type*} (mul : S → S → S)
    (factor : C → S) (D : ℕ) (cs : List C) (a : S) :
    SubexpLocalCorrectionAlgebra.localProduct mul factor D cs a =
      cs.foldl (fun x c => ((fun y => mul y (factor c))^[D]) x) a := by
  induction cs generalizing a with
  | nil => rfl
  | cons c cs ih =>
      rw [SubexpLocalCorrectionAlgebra.localProduct, ih, repeatProduct_eq_iterate]
      rfl

theorem scan_denote {S C R : Type*} [CommRing R]
    (D : ℕ) (denote : S → R[X]) (mul : S → S → S)
    (hmul : ∀ x y, denote (mul x y) = Truncation.trunc D (denote x * denote y))
    (factor : C → S) (F : C → R[X])
    (hf : ∀ c, denote (factor c) = Truncation.trunc D (F c))
    (cs : List C) (skip : List Bool) (a : S) (P : R[X])
    (ha : denote a = Truncation.trunc D P) :
    denote (SubexpNodeScanControl.run
      (fun x c => ((fun y => mul y (factor c))^[D]) x) cs ⟨a, skip, true⟩).value =
      Truncation.trunc D (P * (((cs.eraseIdx skip.length).map (fun c => F c ^ D)).prod)) := by
  rw [SubexpNodeScanControl.run_skip_index, ← localProduct_eq_foldl]
  exact SubexpLocalCorrectionAlgebra.localProduct_denote D denote mul hmul factor F hf
    (cs.eraseIdx skip.length) a P ha

theorem get_mul_prod_eraseIdx {M : Type*} [CommMonoid M]
    (xs : List M) (i : ℕ) (hi : i < xs.length) :
    xs[i] * (xs.eraseIdx i).prod = xs.prod := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          have hi' : i < xs.length := by simpa using hi
          change xs[i] * (a * (xs.eraseIdx i).prod) = a * xs.prod
          rw [mul_left_comm, ih i hi']

/-- Deleting the indexed node from the physical list yields exactly the
Finset cofactor product. Cancellation uses the coefficient shift by X^D,
which is injective over every commutative ring, including rings with zero
divisors. -/
theorem product_excluding_node {R : Type*} [CommRing R] {Q : ℕ}
    (theta : Fin Q → R) (D : ℕ) (i : Fin Q) :
    (((List.ofFn theta).eraseIdx i.val).map
      (fun x => (X + C (theta i - x)) ^ D)).prod =
      TruncatedInverse.localFactor theta D i := by
  classical
  let G : R → R[X] := fun x => (X + C (theta i - x)) ^ D
  have hi : i.val < ((List.ofFn theta).map G).length := by simp
  have hs := get_mul_prod_eraseIdx ((List.ofFn theta).map G) i.val hi
  have hget : ((List.ofFn theta).map G)[i.val] = (X : R[X]) ^ D := by
    simp [G]
  have htotal : ((List.ofFn theta).map G).prod = ∏ j, G (theta j) := by
    rw [List.map_ofFn, List.prod_ofFn]
    rfl
  rw [hget, List.eraseIdx_map, htotal] at hs
  have ht : (X : R[X]) ^ D * (∏ j ∈ Finset.univ.erase i, G (theta j)) = ∏ j, G (theta j) := by
    simpa [G] using Finset.mul_prod_erase Finset.univ (fun j => G (theta j)) (Finset.mem_univ i)
  rw [SubexpLocalFactorAlgebra.localFactor_eq_product]
  change (((List.ofFn theta).eraseIdx i.val).map G).prod = ∏ j ∈ Finset.univ.erase i, G (theta j)
  ext k
  have hc := congrArg (fun p : R[X] => p.coeff (k + D)) (hs.trans ht.symm)
  simpa only [coeff_X_pow_mul] using hc

end SubexponentialSAT.SubexpLocalProductAlgebra

end OAI.Algorithms
