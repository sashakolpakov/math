import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheInitialize
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheFold

namespace OAI.Algorithms

/-!
# Exact meaning of the executed Lagrange product fold

The word recurrence and truncated polynomial accumulator are the values
computed by the physical cache loops. Their interpretation is the ordered
product over the visited integer labels, omitting the distinguished label.
At length p the numerator has degree below p, so the final truncation loses
no coefficient. This file introduces no execution or runtime assumption.
-/

noncomputable section

namespace SubexponentialSAT.SubexpLagrangeCacheSemantics

open Polynomial
open SubexpLiftRing SubexpQuarticRing SubexpLagrangeCacheState
open SubexpLagrangeCacheAlgebra SubexpTruncatedGeometric

section Values

variable (p μ : ℕ) [Fact p.Prime]

def value (c : Fin 4 → ZMod (p ^ μ)) (a : Coefficient p μ) :
    LiftRing.Extension (QuarticSearch.poly c) :=
  quotientDenote c (a.map (wordValue p μ))

def polyValue (c : Fin 4 → ZMod (p ^ μ)) (xs : List (Coefficient p μ)) :
    Polynomial (LiftRing.Extension (QuarticSearch.poly c)) :=
  PolynomialAlgorithm.denote (xs.map (value p μ c))

variable (M : SubexpPreparedQuartic.Modulus p μ) (c : Fin 4 → ZMod (p ^ μ))

theorem difference_value (minusOne : Word (baseWidth p μ))
    (hminus : wordValue p μ minusOne = -1) (a b : Coefficient p μ) :
    value p μ c (SubexpLagrangeCacheProduct.difference p μ M minusOne a b) =
      value p μ c a - value p μ c b :=
  SubexpLocalLinearFactorProgram.difference_denote p μ M c minusOne hminus a b

theorem denominator_value (t : Coefficient p μ)
    (ht : t.map (wordValue p μ) = reductionData c)
    (minusOne : Word (baseWidth p μ)) (hminus : wordValue p μ minusOne = -1)
    (a i j : Coefficient p μ) :
    value p μ c (SubexpLagrangeCacheProduct.denominator p μ M t minusOne a i j) =
      value p μ c a * (value p μ c i - value p μ c j) :=
  (SubexpPreparedQuartic.binaryMul_quotient p μ M c t a
    (SubexpLagrangeCacheProduct.difference p μ M minusOne i j) ht).trans
      (congrArg (fun x => value p μ c a * x)
        (difference_value p μ M c minusOne hminus i j))

theorem factor_value (zero one : Coefficient p μ)
    (hz : value p μ c zero = 0) (ho : value p μ c one = 1)
    (minusOne : Word (baseWidth p μ)) (hminus : wordValue p μ minusOne = -1)
    (j : Coefficient p μ) (D : ℕ) :
    polyValue p μ c (SubexpLagrangeCacheProduct.factor p μ M minusOne zero j one D) =
      Truncation.trunc D (X - C (value p μ c j)) := by
  have h := SubexpLocalLinearFactorProgram.factor_denote p μ M c minusOne hminus
    zero zero j one hz ho D
  change polyValue p μ c (SubexpLagrangeCacheProduct.factor p μ M minusOne zero j one D) =
    Truncation.trunc D (X + C (value p μ c zero - value p μ c j)) at h
  rw [hz, zero_sub, map_neg] at h
  simpa only [sub_eq_add_neg] using h

theorem polynomial_value (t zero one : Coefficient p μ)
    (ht : t.map (wordValue p μ) = reductionData c)
    (hz : value p μ c zero = 0) (ho : value p μ c one = 1)
    (minusOne : Word (baseWidth p μ)) (hminus : wordValue p μ minusOne = -1)
    (j : Coefficient p μ) (D : ℕ) (P : List (Coefficient p μ)) :
    polyValue p μ c (SubexpLagrangeCacheProduct.polynomial p μ M t zero one minusOne j D P) =
      Truncation.trunc D (polyValue p μ c P * (X - C (value p μ c j))) := by
  have h := SubexpTruncatedMultiply.result_correct p μ M c t zero ht hz D P
    (SubexpLagrangeCacheProduct.factor p μ M minusOne zero j one D)
  change polyValue p μ c
    (SubexpLagrangeCacheProduct.polynomial p μ M t zero one minusOne j D P) =
      Truncation.trunc D (polyValue p μ c P *
        polyValue p μ c (SubexpLagrangeCacheProduct.factor p μ M minusOne zero j one D)) at h
  rw [factor_value p μ M c zero one hz ho minusOne hminus j D,
    trunc_mul_trunc_right] at h
  exact h

omit [Fact p.Prime] in
theorem initial_polynomial (zero one : Coefficient p μ)
    (hz : value p μ c zero = 0) (ho : value p μ c one = 1) (D : ℕ) :
    polyValue p μ c (SubexpLagrangeCacheInitialize.initial p μ D zero one).polynomial =
      Truncation.trunc D 1 := by
  have h := SubexpLocalCorrectionAlgebra.padded_denote (value p μ c) zero one zero hz D
  simpa only [SubexpLagrangeCacheInitialize.initial, polyValue, ho, hz,
    map_one, map_zero, mul_zero, add_zero] using h

end Values

section Fold

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
variable (c : Fin 4 → ZMod (p ^ μ)) (t zero one : Coefficient p μ)
variable (ht : t.map (wordValue p μ) = reductionData c)
variable (hz : value p μ c zero = 0) (ho : value p μ c one = 1)
variable (minusOne : Word (baseWidth p μ)) (hminus : wordValue p μ minusOne = -1)

local notation "R" => LiftRing.Extension (QuarticSearch.poly c)

include ht hz ho hminus

theorem run_denominator (D i j n : ℕ) (a : Partial p μ D) :
    value p μ c (run p μ M D t zero one minusOne i j n a).denominator =
      value p μ c a.denominator *
        orderedProduct (fun k : ℕ => (i : R) - (k : R)) i (List.range' j n) := by
  have hlabel (k : ℕ) : value p μ c (label p μ M zero one k) = (k : R) :=
    SubexpLagrangeCacheState.label_value p μ M c zero one hz ho k
  induction n generalizing j a with
  | zero => simp [run, orderedProduct]
  | succ n ih =>
      rw [run, ih, orderedProduct_range_succ]
      by_cases hij : i = j
      · simp [advance, hij]
      · simp only [advance, ite_eq_right hij, denominator_value p μ M c t ht minusOne hminus,
          hlabel, mul_assoc]

theorem run_polynomial (D i j n : ℕ) (a : Partial p μ D) (P : R[X])
    (ha : polyValue p μ c a.polynomial = Truncation.trunc D P) :
    polyValue p μ c (run p μ M D t zero one minusOne i j n a).polynomial =
      Truncation.trunc D
        (P * orderedProduct (fun k : ℕ => (X : R[X]) - C (k : R)) i (List.range' j n)) := by
  induction n generalizing j a P with
  | zero => simpa [run, orderedProduct] using ha
  | succ n ih =>
      rw [run, orderedProduct_range_succ]
      by_cases hij : i = j
      · simp only [advance, ite_eq_left hij, one_mul]
        exact ih j.succ a P ha
      · have hnext : polyValue p μ c
            (advance p μ M D t zero one minusOne i j a).polynomial =
            Truncation.trunc D (P * (X - C (j : R))) := by
          simp only [advance, ite_eq_right hij]
          rw [polynomial_value p μ M c t zero one ht hz ho minusOne hminus,
            show value p μ c (label p μ M zero one j) = (j : R) from
              SubexpLagrangeCacheState.label_value p μ M c zero one hz ho j, ha]
          simpa only [mul_comm] using
            (trunc_mul_trunc_right D (X - C (j : R)) P)
        simpa only [ite_eq_right hij, mul_assoc] using
          ih (j + 1) (advance p μ M D t zero one minusOne i j a)
            (P * (X - C (j : R))) hnext

theorem run_denominator_eq (i : Fin p) :
    value p μ c
      (run p μ M p t zero one minusOne i.val 0 p
        (SubexpLagrangeCacheInitialize.initial p μ p zero one)).denominator =
      SubexpLagrangeCacheAlgebra.denominator (fun j : Fin p => (j.val : R)) i := by
  rw [run_denominator p μ M c t zero one ht hz ho minusOne hminus]
  change value p μ c one * _ = _
  rw [ho, one_mul, ← List.range_eq_range', orderedProduct_range, orderedProduct_finRange]
  rfl

theorem run_numerator_truncated (i : Fin p) :
    polyValue p μ c
      (run p μ M p t zero one minusOne i.val 0 p
        (SubexpLagrangeCacheInitialize.initial p μ p zero one)).polynomial =
      Truncation.trunc p
        (numerator (fun j : Fin p => (j.val : R)) i) := by
  rw [run_polynomial p μ M c t zero one ht hz ho minusOne hminus p i.val 0 p
    (SubexpLagrangeCacheInitialize.initial p μ p zero one) 1
      (initial_polynomial p μ c zero one hz ho p)]
  rw [one_mul, ← List.range_eq_range', orderedProduct_range, orderedProduct_finRange]
  rfl

/-- All p stored coefficients are sufficient: one factor is skipped. -/
theorem run_numerator (i : Fin p) :
    polyValue p μ c
      (run p μ M p t zero one minusOne i.val 0 p
        (SubexpLagrangeCacheInitialize.initial p μ p zero one)).polynomial =
      numerator (fun j : Fin p => (j.val : R)) i := by
  rw [run_numerator_truncated p μ M c t zero one ht hz ho minusOne hminus]
  exact trunc_numerator (Fact.out : p.Prime).pos _ i

end Fold

section ActualRing

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
variable (t zero one : Coefficient p μ)
variable (ht : t.map (wordValue p μ) = reductionData (QuarticSearch.liftedCoefficients p μ))
variable (hz : value p μ (QuarticSearch.liftedCoefficients p μ) zero = 0)
variable (ho : value p μ (QuarticSearch.liftedCoefficients p μ) one = 1)
variable (minusOne : Word (baseWidth p μ)) (hminus : wordValue p μ minusOne = -1)

include ht hz ho hminus

theorem actual_run_denominator (i : Fin p) :
    value p μ (QuarticSearch.liftedCoefficients p μ)
      (run p μ M p t zero one minusOne i.val 0 p
        (SubexpLagrangeCacheInitialize.initial p μ p zero one)).denominator =
      SubexpLagrangeCacheAlgebra.denominator (integerNodes p μ) i :=
  run_denominator_eq p μ M (QuarticSearch.liftedCoefficients p μ)
    t zero one ht hz ho minusOne hminus i

theorem actual_run_numerator (i : Fin p) :
    polyValue p μ (QuarticSearch.liftedCoefficients p μ)
      (run p μ M p t zero one minusOne i.val 0 p
        (SubexpLagrangeCacheInitialize.initial p μ p zero one)).polynomial =
      numerator (integerNodes p μ) i :=
  run_numerator p μ M (QuarticSearch.liftedCoefficients p μ)
    t zero one ht hz ho minusOne hminus i

end ActualRing

end SubexponentialSAT.SubexpLagrangeCacheSemantics

end

end OAI.Algorithms
