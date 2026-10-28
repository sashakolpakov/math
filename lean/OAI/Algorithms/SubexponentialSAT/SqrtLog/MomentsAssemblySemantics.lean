import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramProductSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsFinite

namespace OAI.Algorithms

/-! Denotation of the pure recurrences executed by the native assembly loop.
The local assignment worker is a parameter here; its concrete correctness
contract is supplied by the assignment implementation. -/
namespace SubexponentialSAT.SqrtLog.MomentsAssembly

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators

variable {R : Type*} [CommRing R]
variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
  (cache : RingProgram.ScalarCache p t) {n d : ℕ}
  (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)

abbrev coefficient := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis

noncomputable def denote (entries : List (Product.Entry n (baseWidth p t) d)) : Jet (Fin n) R :=
  Sparse.denote (Dictionary.denoteTable (coefficient p t M cache scalar basis) entries)

@[simp] theorem denote_nil : denote p t M cache scalar basis
    ([] : List (Product.Entry n (baseWidth p t) d)) = 0 := rfl

variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
  (htable : ∀ i j, basis i * basis j =
    ∑ k, scalar (SubexpQuarticRing.wordValue p t (table i j k)) * basis k)

include htable in
theorem weightedValue_denote
    (weight : RingProgram.Code (Word (baseWidth p t)) d)
    (jet seed : List (Product.Entry n (baseWidth p t) d))
    (hn : (Sparse.keys seed).Nodup) :
    denote p t M cache scalar basis (weightedValue p t M cache table weight jet seed) =
      Moments.ringScalar (coefficient p t M cache scalar basis weight) *
        denote p t M cache scalar basis jet + denote p t M cache scalar basis seed := by
  unfold weightedValue denote Sparse.denote
  rw [Normalize.run_decode p t M cache scalar basis Sparse.atom
    Sparse.atom_zero Sparse.atom_add _ seed hn]
  change Sparse.denote _ + _ = _
  rw [Moments.ringScalar_eq_atom]
  congr 1
  exact Squarefree.ScaleProgram.denote_scaled p t M cache scalar basis table htable weight jet

theorem weightedValue_nodup
    (weight : RingProgram.Code (Word (baseWidth p t)) d)
    (jet seed : List (Product.Entry n (baseWidth p t) d))
    (hn : (Sparse.keys seed).Nodup) :
    (Sparse.keys (weightedValue p t M cache table weight jet seed)).Nodup :=
  Normalize.run_nodup p t M cache _ seed hn

noncomputable def contributionDenote (a : Contribution n (baseWidth p t) d) : Jet (Fin n) R :=
  Moments.ringScalar (coefficient p t M cache scalar basis a.1) *
    denote p t M cache scalar basis a.2

/-- The concrete weight and local-jet workers discharge the record contract
independently. -/
theorem contributionDenote_eq (a : Contribution n (baseWidth p t) d)
    (w : R) (f : Jet (Fin n) R)
    (hw : coefficient p t M cache scalar basis a.1 = w)
    (hf : denote p t M cache scalar basis a.2 = f) :
    contributionDenote p t M cache scalar basis a = Moments.ringScalar w * f := by
  simp only [contributionDenote, hw, hf]

variable (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)

theorem headRun_nodup (c : AssignmentContext) (xs : List (List Bool))
    (seed : List (Product.Entry n (baseWidth p t) d)) (hn : (Sparse.keys seed).Nodup) :
    (Sparse.keys (headRun p t M cache table meaning c xs seed)).Nodup := by
  induction xs generalizing seed with
  | nil => exact hn
  | cons x xs ih =>
    exact ih _ (weightedValue_nodup p t M cache table _ _ seed hn)

include htable in
theorem headRun_denote (c : AssignmentContext) (xs : List (List Bool))
    (seed : List (Product.Entry n (baseWidth p t) d)) (hn : (Sparse.keys seed).Nodup) :
    denote p t M cache scalar basis (headRun p t M cache table meaning c xs seed) =
      (xs.map fun x => contributionDenote p t M cache scalar basis (meaning c x)).sum +
        denote p t M cache scalar basis seed := by
  induction xs generalizing seed with
  | nil => simp [headRun]
  | cons x xs ih =>
    rw [headRun, ih _ (weightedValue_nodup p t M cache table _ _ seed hn),
      weightedValue_denote p t M cache scalar basis table htable
        (meaning c x).1 (meaning c x).2 seed hn]
    simp only [List.map_cons, List.sum_cons, contributionDenote]
    simp only [add_assoc]
    exact add_left_comm _ _ _

noncomputable def headDenote (high : Fin 768 → List Bool) (h : HeadInput) : Jet (Fin n) R :=
  (h.assignments.map fun x =>
    contributionDenote p t M cache scalar basis (meaning (headContext high h) x)).sum

include htable in
theorem headStepValue_denote (u J : ℕ) (high : Fin 768 → List Bool) (h : HeadInput)
    (left : List (Product.Entry n (baseWidth p t) d)) :
    denote p t M cache scalar basis (headStepValue p t M cache table u J meaning high h left) =
      canonical u J (denote p t M cache scalar basis left *
        headDenote p t M cache scalar basis meaning high h) := by
  unfold headStepValue denote
  rw [Product.run_denote p t M cache scalar basis table htable u J _ _ [] (by simp [Sparse.keys])]
  change canonical u J (denote p t M cache scalar basis left *
    denote p t M cache scalar basis (headRun p t M cache table meaning _ _ [])) + 0 = _
  rw [headRun_denote p t M cache scalar basis table htable meaning _ _ [] (by simp [Sparse.keys])]
  simp only [denote_nil, add_zero, headDenote]
  rfl

theorem headStepValue_nodup (u J : ℕ) (high : Fin 768 → List Bool) (h : HeadInput)
    (left : List (Product.Entry n (baseWidth p t) d)) :
    (Sparse.keys (headStepValue p t M cache table u J meaning high h left)).Nodup :=
  Product.run_nodup p t M cache table u J _ _ [] (by simp [Sparse.keys])

theorem headsRun_nodup (u J : ℕ) (high : Fin 768 → List Bool) (hs : List HeadInput)
    (left : List (Product.Entry n (baseWidth p t) d)) (hn : (Sparse.keys left).Nodup) :
    (Sparse.keys (headsRun p t M cache table u J meaning high hs left)).Nodup := by
  induction hs generalizing left with
  | nil => exact hn
  | cons h hs ih => exact ih _ (headStepValue_nodup p t M cache table meaning u J high h left)

include htable in
theorem headsRun_denote (u J : ℕ) (high : Fin 768 → List Bool) (hs : List HeadInput)
    (left : List (Product.Entry n (baseWidth p t) d))
    (hl : canonical u J (denote p t M cache scalar basis left) =
      denote p t M cache scalar basis left) :
    denote p t M cache scalar basis (headsRun p t M cache table u J meaning high hs left) =
      canonical u J (denote p t M cache scalar basis left *
        (hs.map (headDenote p t M cache scalar basis meaning high)).prod) := by
  induction hs generalizing left with
  | nil => simpa [headsRun] using hl.symm
  | cons h hs ih =>
    rw [headsRun]
    have hd := headStepValue_denote p t M cache scalar basis table htable meaning u J high h left
    rw [ih _ (by rw [hd, Moments.canonical_idempotent]), hd,
      Moments.canonical_mul_left]
    simp only [List.map_cons, List.prod_cons, mul_assoc]

theorem rawProject_decoded (s : Finset (Fin n))
    (entries : List (Product.Entry n (baseWidth p t) d)) :
    Dictionary.denoteTable (coefficient p t M cache scalar basis) (Moments.rawProject s entries) =
      Moments.rawProject s (Dictionary.denoteTable (coefficient p t M cache scalar basis) entries) := by
  induction entries with
  | nil => rfl
  | cons a entries ih =>
    by_cases h : a.1.vars = s <;> simp [Moments.rawProject, Dictionary.denoteTable, h]
    all_goals exact ih

theorem supportValue_denote (s : Finset (Fin n))
    (product seed : List (Product.Entry n (baseWidth p t) d)) (hn : (Sparse.keys seed).Nodup) :
    denote p t M cache scalar basis (supportValue p t M cache s product seed) =
      Moments.projectSupport s (denote p t M cache scalar basis product) +
        denote p t M cache scalar basis seed := by
  unfold supportValue denote Sparse.denote
  rw [Normalize.run_decode p t M cache scalar basis Sparse.atom
    Sparse.atom_zero Sparse.atom_add _ seed hn]
  change Sparse.denote _ + _ = _
  rw [rawProject_decoded, Moments.denote_rawProject]

theorem supportValue_nodup (s : Finset (Fin n))
    (product seed : List (Product.Entry n (baseWidth p t) d)) (hn : (Sparse.keys seed).Nodup) :
    (Sparse.keys (supportValue p t M cache s product seed)).Nodup :=
  Normalize.run_nodup p t M cache _ seed hn

end SubexponentialSAT.SqrtLog.MomentsAssembly

end OAI.Algorithms
