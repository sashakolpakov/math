import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLocalFactorAlgebra
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionAlgebra
import OAI.Algorithms.SubexponentialSAT.SubexpResidueInverse

namespace OAI.Algorithms

/-! Semantic invariants for the fixed-width local CRT preparation. Every
intermediate polynomial product may be truncated to D coefficients. The
constant coefficient is inverted once by the executable residue algorithm. -/

namespace SubexponentialSAT.SubexpLocalCorrectionAlgebra

open Polynomial
open scoped BigOperators
open SubexpTruncatedGeometric

def padded {C : Type*} (zero low high : C) : ℕ → List C
  | 0 => []
  | 1 => [low]
  | n + 2 => low :: high :: List.replicate n zero

@[simp] theorem padded_length {C : Type*} (zero low high : C) (D : ℕ) :
    (padded zero low high D).length = D := by
  cases D with
  | zero => rfl
  | succ D => cases D <;> simp [padded]

theorem padded_denote {C R : Type*} [CommRing R]
    (decode : C → R) (zero low high : C) (hz : decode zero = 0) (D : ℕ) :
    PolynomialAlgorithm.denote ((padded zero low high D).map decode) =
      Truncation.trunc D (Polynomial.C (decode low) + X * Polynomial.C (decode high)) := by
  cases D with
  | zero => simp [padded, SubexpConvolutionAlgebra.trunc_zero_order]
  | succ D =>
      cases D with
      | zero =>
          ext k
          cases k <;> simp [padded, Truncation.coeff_trunc, PolynomialAlgorithm.denote_cons
            ]
      | succ n =>
          simp only [padded, List.map_cons, List.map_replicate, hz,
            PolynomialAlgorithm.denote_cons, SubexpConvolutionAlgebra.denote_replicate_zero,
            mul_zero, add_zero]
          ext k
          cases k with
          | zero => simp [Truncation.coeff_trunc]
          | succ k => cases k <;> simp [Truncation.coeff_trunc ]

/-- Tail-recursive repeated multiplication, with one cached accumulator. -/
def repeatProduct {S : Type*} (mul : S → S → S) (factor : S) : ℕ → S → S
  | 0, acc => acc
  | n + 1, acc => repeatProduct mul factor n (mul acc factor)

/-- Scan the supplied other nodes and multiply each local linear factor D
times. This is the value-level schedule of the physical node/power loops. -/
def localProduct {C S : Type*} (mul : S → S → S) (factor : C → S) (D : ℕ) :
    List C → S → S
  | [], acc => acc
  | c :: cs, acc => localProduct mul factor D cs (repeatProduct mul (factor c) D acc)

section TruncatedProducts

variable {S C R : Type*} [CommRing R]
variable (D : ℕ) (denote : S → R[X]) (mul : S → S → S)
variable (hmul : ∀ x y, denote (mul x y) = Truncation.trunc D (denote x * denote y))

include hmul

theorem repeatProduct_denote (factor acc : S) (F P : R[X])
    (hf : denote factor = Truncation.trunc D F)
    (ha : denote acc = Truncation.trunc D P) (n : ℕ) :
    denote (repeatProduct mul factor n acc) = Truncation.trunc D (P * F ^ n) := by
  induction n generalizing acc P with
  | zero => simpa [repeatProduct] using ha
  | succ n ih =>
      have hnext : denote (mul acc factor) = Truncation.trunc D (P * F) := by
        rw [hmul, ha, hf, trunc_mul_trunc]
      rw [repeatProduct, ih (mul acc factor) (P * F) hnext]
      congr 1
      rw [pow_succ]
      ring

theorem localProduct_denote (factor : C → S) (F : C → R[X])
    (hf : ∀ c, denote (factor c) = Truncation.trunc D (F c))
    (cs : List C) (acc : S) (P : R[X]) (ha : denote acc = Truncation.trunc D P) :
    denote (localProduct mul factor D cs acc) =
      Truncation.trunc D (P * (cs.map (fun c => F c ^ D)).prod) := by
  induction cs generalizing acc P with
  | nil => simpa [localProduct] using ha
  | cons c cs ih =>
      have hnext := repeatProduct_denote D denote mul hmul (factor c) acc
        (F c) P (hf c) ha D
      rw [localProduct, ih _ _ hnext]
      simp only [List.map_cons, List.prod_cons, mul_assoc]

end TruncatedProducts

/-- Finish the local inverse and multiply it by the supplied jet. -/
def correctionFromLoop {S : Type*} (D : ℕ) (zero one z ca : S)
    (add mul : S → S → S) (jet : S) : S :=
  let series := (TruncatedInverse.geometricLoop zero one add mul z D).2
  mul jet (mul ca series)

theorem correctionFromLoop_denote {S R : Type*} [CommRing R]
    (D : ℕ) (zero one z ca jet : S) (add mul : S → S → S)
    (denote : S → R[X]) (P J : R[X]) (a : R)
    (hzero : denote zero = 0) (hone : denote one = Truncation.trunc D 1)
    (hz : denote z = Truncation.trunc D (1 - C a * P))
    (hca : denote ca = Truncation.trunc D (C a)) (hjet : denote jet = J)
    (hadd : ∀ x y, denote (add x y) = denote x + denote y)
    (hmul : ∀ x y, denote (mul x y) = Truncation.trunc D (denote x * denote y)) :
    denote (correctionFromLoop D zero one z ca add mul jet) =
      TruncatedInverse.correctedJet P J a D := by
  let series := (TruncatedInverse.geometricLoop zero one add mul z D).2
  have hs : denote series = Truncation.trunc D
      (∑ j ∈ Finset.range D, (1 - C a * P) ^ j) :=
    (SubexpTruncatedGeometric.geometricLoop_denote D zero one z add mul denote _
      hzero hone hz hadd hmul D).2
  have hinv : denote (mul ca series) = TruncatedInverse.inverse P a D := by
    rw [hmul, hca, hs, trunc_mul_trunc]
    rfl
  change denote (mul jet (mul ca series)) = _
  rw [hmul, hjet, hinv]
  rfl

section ConstantInverse

variable {A E ι : Type*} [CommRing A] [Field E] [Fintype E]
variable [Fintype ι] [DecidableEq ι]

/-- The computed inverse of the truncated local factor's constant term is
also the exact constant inverse required by the established CRT formula. -/
theorem computed_constantInverse (ρ : A →+* E) (q : ℕ) (hq : Fintype.card E = q)
    (π : A) (μ : ℕ) (hπ : π ^ μ = 0) (hker : ∀ x, ρ x = 0 → π ∣ x)
    (θ : ι → A) (hθ : Function.Injective (fun i => ρ (θ i)))
    (D : ℕ) (hD : 0 < D) (i : ι) :
    (SubexpResidueInverse.inverseWithCost q μ
      ((Truncation.trunc D (TruncatedInverse.localFactor θ D i)).coeff 0)).1 *
        (TruncatedInverse.localFactor θ D i).coeff 0 = 1 := by
  have h := SubexpResidueInverse.inverseWithCost_correct ρ q hq π μ hπ hker
    ((Truncation.trunc D (TruncatedInverse.localFactor θ D i)).coeff 0)
    (SubexpLocalFactorAlgebra.residue_truncated_localFactor_coeff_ne_zero ρ θ hθ D hD i)
  simpa only [Truncation.coeff_trunc, ite_eq_left hD] using h

end ConstantInverse

end SubexponentialSAT.SubexpLocalCorrectionAlgebra

end OAI.Algorithms
