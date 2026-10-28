import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblySemantics

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsAssembly
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators

variable {R : Type*} [CommRing R]
variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
  (cache : RingProgram.ScalarCache p t) {n d : ℕ}
  (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
  (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
  (htable : ∀ i j, basis i * basis j =
    ∑ k, scalar (SubexpQuarticRing.wordValue p t (table i j k)) * basis k)
  (u J : ℕ)
  (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)

noncomputable def supportDenote (high : Fin 768 → List Bool) (hs : List HeadInput)
    (s : Finset (Fin n)) : Jet (Fin n) R :=
  Moments.projectSupport s (canonical u J
    ((hs.map (headDenote p t M cache scalar basis meaning
      (Function.update high 168 (encodeMask s)))).prod))

include htable in
theorem supportProduct_denote (high : Fin 768 → List Bool) (hs : List HeadInput)
    (one : List (Product.Entry n (baseWidth p t) d)) (s : Finset (Fin n))
    (ho : denote p t M cache scalar basis one = canonical u J 1) :
    denote p t M cache scalar basis (supportProduct p t M cache table u J meaning high hs one s) =
      canonical u J ((hs.map (headDenote p t M cache scalar basis meaning
        (Function.update high 168 (encodeMask s)))).prod) := by
  rw [supportProduct, headsRun_denote p t M cache scalar basis table htable meaning u J _ hs one
    (by rw [ho, Moments.canonical_idempotent]), ho, Moments.canonical_mul_left, one_mul]

theorem supportsRun_nodup (high : Fin 768 → List Bool) (hs : List HeadInput)
    (one : List (Product.Entry n (baseWidth p t) d)) (ss : List (Finset (Fin n)))
    (seed : List (Product.Entry n (baseWidth p t) d)) (hn : (Sparse.keys seed).Nodup) :
    (Sparse.keys (supportsRun p t M cache table u J meaning high hs one ss seed)).Nodup := by
  induction ss generalizing seed with
  | nil => exact hn
  | cons s ss ih => exact ih _ (supportValue_nodup p t M cache s _ seed hn)

include htable in
theorem supportsRun_denote (high : Fin 768 → List Bool) (hs : List HeadInput)
    (one : List (Product.Entry n (baseWidth p t) d)) (ss : List (Finset (Fin n)))
    (seed : List (Product.Entry n (baseWidth p t) d)) (hn : (Sparse.keys seed).Nodup)
    (ho : denote p t M cache scalar basis one = canonical u J 1) :
    denote p t M cache scalar basis (supportsRun p t M cache table u J meaning high hs one ss seed) =
      (ss.map (supportDenote p t M cache scalar basis u J meaning high hs)).sum +
        denote p t M cache scalar basis seed := by
  induction ss generalizing seed with
  | nil => simp [supportsRun]
  | cons s ss ih =>
    rw [supportsRun, ih _ (supportValue_nodup p t M cache s _ seed hn),
      supportValue_denote p t M cache scalar basis s _ seed hn,
      supportProduct_denote p t M cache scalar basis table htable u J meaning high hs one s ho]
    simp only [List.map_cons, List.sum_cons, supportDenote]
    simp only [add_assoc]
    exact add_left_comm _ _ _

theorem bucketsRun_nodup (high : Fin 768 → List Bool) (ss : List (Finset (Fin n)))
    (one : List (Product.Entry n (baseWidth p t) d)) (bs : List BucketInput)
    (seed : List (Product.Entry n (baseWidth p t) d)) (hn : (Sparse.keys seed).Nodup) :
    (Sparse.keys (bucketsRun p t M cache table u J meaning high ss one bs seed)).Nodup := by
  induction bs generalizing seed with
  | nil => exact hn
  | cons b bs ih => exact ih _ (supportsRun_nodup p t M cache table u J meaning _ _ one ss seed hn)

include htable in
theorem bucketsRun_denote (high : Fin 768 → List Bool) (ss : List (Finset (Fin n)))
    (one : List (Product.Entry n (baseWidth p t) d)) (bs : List BucketInput)
    (seed : List (Product.Entry n (baseWidth p t) d)) (hn : (Sparse.keys seed).Nodup)
    (ho : denote p t M cache scalar basis one = canonical u J 1) :
    denote p t M cache scalar basis (bucketsRun p t M cache table u J meaning high ss one bs seed) =
      (bs.map fun b => (ss.map (supportDenote p t M cache scalar basis u J meaning
        (Function.update high 177 b.context) b.heads)).sum).sum +
          denote p t M cache scalar basis seed := by
  induction bs generalizing seed with
  | nil => simp [bucketsRun]
  | cons b bs ih =>
    rw [bucketsRun, ih _ (supportsRun_nodup p t M cache table u J meaning _ _ one ss seed hn),
      supportsRun_denote p t M cache scalar basis table htable u J meaning _ _ one ss seed hn ho]
    simp only [List.map_cons, List.sum_cons]
    simp only [add_assoc]
    exact add_left_comm _ _ _

/- Exact interface to a finite-record run. The premise identifies only each
local head sum; no global assignment tuple or moment answer is assumed. -/
include htable in
theorem supportsRun_eq_run {vars : Finset (Fin n)}
    (high : Fin 768 → List Bool) (hs : List HeadInput)
    (one : List (Product.Entry n (baseWidth p t) d)) (ss : List (Finset (Fin n)))
    (ho : denote p t M cache scalar basis one = canonical u J 1)
    (data : Finset (Fin n) → List (List (R × Moments.Stored (R := R) vars u J)))
    (hd : ∀ s ∈ ss,
      (hs.map (headDenote p t M cache scalar basis meaning
        (Function.update high 168 (encodeMask s)))) =
      ((data s).map fun l => (l.map fun a => Moments.ringScalar a.1 * a.2.denote).sum)) :
    denote p t M cache scalar basis (supportsRun p t M cache table u J meaning high hs one ss []) =
      Moments.Stored.denote (MomentsAlgorithm.run Moments.Stored.ops data ss).1 := by
  rw [supportsRun_denote p t M cache scalar basis table htable u J meaning high hs one ss []
    (by simp [Sparse.keys]) ho, denote_nil, add_zero,
    MomentsAlgorithm.run_canonical
      (Moments.Stored.ops (R := R) (vars := vars) (t := u) (J := J))
      Moments.Stored.denote (Moments.ringScalar (V := Fin n) (R := R))
      (Moments.projectSupport (V := Fin n) (R := R)) (canonical u J)
      Moments.Stored.ops_correct data ss]
  induction ss with
  | nil => simp
  | cons s ss ih =>
    have hs := hd s (by simp)
    have ht := ih (fun q hq => hd q (by simp [hq]))
    simp only [List.map_cons, List.sum_cons, map_add, supportDenote] at ht ⊢
    rw [hs, Moments.projectSupport_canonical, ht]

include htable in
theorem supportsRun_output_eq_run {vars : Finset (Fin n)}
    (high : Fin 768 → List Bool) (hs : List HeadInput)
    (one : List (Product.Entry n (baseWidth p t) d)) (ss : List (Finset (Fin n)))
    (ho : denote p t M cache scalar basis one = canonical u J 1)
    (data : Finset (Fin n) → List (List (R × Moments.Stored (R := R) vars u J)))
    (hd : ∀ s ∈ ss,
      (hs.map (headDenote p t M cache scalar basis meaning
        (Function.update high 168 (encodeMask s)))) =
      ((data s).map fun l => (l.map fun a => Moments.ringScalar a.1 * a.2.denote).sum)) :
    PolynomialAlgorithm.denote (Moments.outputCoefficients u J
      (MomentsProgram.Dictionary.denoteTable (coefficient p t M cache scalar basis)
        (supportsRun p t M cache table u J meaning high hs one ss []))) =
      PolynomialAlgorithm.denote (Moments.outputCoefficients u J
        (MomentsAlgorithm.run Moments.Stored.ops data ss).1.data) := by
  rw [Moments.outputCoefficients_denote, Moments.outputCoefficients_denote]
  change Truncation.trunc J (Moments.sumUCoeff u (Moments.jetCoeff ⟨∅⟩
    (denote p t M cache scalar basis _))) = _
  rw [supportsRun_eq_run p t M cache scalar basis table htable u J meaning high hs one ss ho data hd]
  rfl

end SubexponentialSAT.SqrtLog.MomentsAssembly

end OAI.Algorithms
