import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMomentPhase
import OAI.Algorithms.SubexponentialSAT.SubexpMomentArray
import OAI.Algorithms.SubexponentialSAT.SubexpJetExecution

namespace OAI.Algorithms

/-!
# Meaning of the concrete moment phase's output array

The phase stores fixed-width quartic words and updates one physical cell per
query. Its exact binary fold is identified here with the previously verified
jet algorithm. The proof permits the actual slot and query orders; neither
needs to be physically reordered to match the mathematical presentation.
-/

namespace SubexponentialSAT.SubexpMomentSemantics

open SymbolicCost SubexpSymbolicCost SubexpQuarticRing SubexpLiftRing
open SubexpExtractionJobs (Query)
open SubexpMomentArray (contents)

noncomputable def decode (p D : ℕ) [Fact p.Prime]
    (c : Fin 4 → ZMod (p ^ (D + 1))) (a : QuarticCode p D) :
    LiftRing.Extension (QuarticSearch.poly c) :=
  quotientDenote c (a.map (wordValue p (D + 1)))

noncomputable def decodedSource (p D : ℕ) [Fact p.Prime]
    (c : Fin 4 → ZMod (p ^ (D + 1)))
    (source : (Fin D → ℕ) → Algorithm.Expr (CoeffList D (QuarticCode p D))) :
    (Fin D → ℕ) → Algorithm.Expr
      (CoeffList D (LiftRing.Extension (QuarticSearch.poly c))) :=
  fun a => (source a).map (fun raw => raw.map (fun term => (term.1, decode p D c term.2)))

theorem decode_zero (p D : ℕ) [Fact p.Prime]
    (c : Fin 4 → ZMod (p ^ (D + 1))) :
    decode p D c (SubexpCoefficientLookup.zeroCoefficient p (D + 1)) = 0 :=
  SubexpCoefficientLookup.zero_quotient p (D + 1) c

section Prepared

variable (p D : ℕ) [Fact p.Prime]
  (M : SubexpPreparedQuartic.Modulus p (D + 1))
  (c : Fin 4 → ZMod (p ^ (D + 1))) (t z o : QuarticCode p D)
  (ht : t.map (wordValue p (D + 1)) = reductionData c)
  (hz : quotientDenote c (z.map (wordValue p (D + 1))) = 0)
  (ho : quotientDenote c (o.map (wordValue p (D + 1))) = 1)
  (slots : List (RawIndex D)) (hn : slots.Nodup)
  (hs : ∀ a, a ∈ slots ↔ Retained D a)
  (source : (Fin D → ℕ) → Algorithm.Expr (CoeffList D (QuarticCode p D)))

local notation "ops" => preparedProgram p D M t z o
local notation "sem" => preparedRing p D M c t z o ht hz ho
local notation "readCells" => contents (decode p D c)

include ht hz ho hn hs in
theorem decoded_coefficient (q : Query D) :
    coeff ((SubexpExecution.programEval ops slots (source q.exponent)).1.map
      (fun term => (term.1, decode p D c term.2))) (q.exponent, (q.u, q.z)) =
      SubexpExtractionJobs.contribution (decodedSource p D c source) q := by
  exact SubexpMomentArray.programEval_contribution sem slots hn hs source q

include ht hz ho hn hs in
/-- The actual full-list lookup yields the required coefficient, including
any duplicate records present before the evaluator's projection. -/
theorem value_decode (q : Query D) :
    decode p D c (SubexpMomentPhase.value p D M t z o slots source q) =
      SubexpExtractionJobs.contribution (decodedSource p D c source) q := by
  change quotientDenote c
      ((SubexpCoefficientLookup.fold p (D + 1) M
        (fixedKey (q.exponent, (q.u, q.z)))
        (SubexpCoefficientLookup.zeroCoefficient p (D + 1))
        (SubexpMomentStep.encodedRecords
          (SubexpExecution.programEval ops slots (source q.exponent)).1)).map
            (wordValue p (D + 1))) = _
  rw [SubexpCoefficientLookup.lookup_quotient]
  exact (SubexpMomentStep.encodedRecords_coeff
    (fun v : QuarticCode p D => quotientDenote c (v.map (wordValue p (D + 1))))
    (SubexpExecution.programEval ops slots (source q.exponent)).1
    (q.exponent, (q.u, q.z))).trans
      (decoded_coefficient p D M c t z o ht hz ho slots hn hs source q)

include ht hz ho hn hs in
/-- One concrete binary update refines the mathematical single-cell sum. -/
theorem contents_step (cells : List (QuarticCode p D)) (q : Query D)
    (hq : q.z < cells.length) :
    readCells (SubexpMomentPhase.step p D M t z o slots source cells q) =
      SubexpJetAccumulator.addAt Query.z
        (SubexpExtractionJobs.contribution (decodedSource p D c source))
        (readCells cells) q := by
  unfold SubexpMomentPhase.step
  rw [SubexpMomentArray.contents_set _ _ _ _ hq]
  unfold SubexpJetAccumulator.addAt
  apply congrArg (Function.update (readCells cells) q.z)
  have hu := SubexpMomentStep.updated_quotient p D M c
    (SubexpExecution.programEval ops slots (source q.exponent)).1
    (q.exponent, (q.u, q.z))
    (cells.getD q.z (SubexpCoefficientLookup.zeroCoefficient p (D + 1)))
  change decode p D c
      (SubexpPreparedQuartic.binaryAdd p (D + 1) M
        (SubexpMomentPhase.value p D M t z o slots source q)
        (cells.getD q.z (SubexpCoefficientLookup.zeroCoefficient p (D + 1)))).1 = _
  change decode p D c
      (SubexpPreparedQuartic.binaryAdd p (D + 1) M
        (SubexpMomentPhase.value p D M t z o slots source q)
        (cells.getD q.z (SubexpCoefficientLookup.zeroCoefficient p (D + 1)))).1 =
    decode p D c (cells.getD q.z (SubexpCoefficientLookup.zeroCoefficient p (D + 1))) +
      coeff ((SubexpExecution.programEval ops slots (source q.exponent)).1.map
        (fun term => (term.1, decode p D c term.2))) (q.exponent, (q.u, q.z)) at hu
  rw [hu, decoded_coefficient p D M c t z o ht hz ho slots hn hs source q,
    ← SubexpMomentArray.contents_getD (decode p D c)
      (SubexpCoefficientLookup.zeroCoefficient p (D + 1)) (decode_zero p D c)]

include ht hz ho hn hs in
theorem contents_fold (qs : List (Query D))
    (valid : ∀ q ∈ qs, q.z < D) (cells : List (QuarticCode p D))
    (hlen : cells.length = D) :
    readCells (qs.foldl (SubexpMomentPhase.step p D M t z o slots source) cells) =
      qs.foldl (SubexpJetAccumulator.addAt Query.z
        (SubexpExtractionJobs.contribution (decodedSource p D c source)))
        (readCells cells) := by
  induction qs generalizing cells with
  | nil => rfl
  | cons q qs ih =>
      have hq : q.z < cells.length := by
        rw [hlen]
        exact valid q (by simp)
      have hrest : ∀ q' ∈ qs, q'.z < D := fun q' hq' => valid q' (by simp [hq'])
      simp only [List.foldl_cons]
      rw [ih hrest _ ((SubexpMomentPhase.step_length p D M t z o slots source cells q).trans hlen),
        contents_step p D M c t z o ht hz ho slots hn hs source cells q hq]

include ht hz ho hn hs in
/-- The exact stored binary fold, started by the physical zero initializer,
decodes to the complete jet. Only the query permutation and local prepared
coefficient data are used; no final-output equality is assumed. -/
theorem fold_eq_rawJet (qs : List (Query D))
    (hqs : qs.Perm (SubexpExtractionJobs.queries D)) :
    (qs.foldl (SubexpMomentPhase.step p D M t z o slots source)
      (SubexpMomentPhase.zeroCells p D)).map (decode p D c) =
        Algorithm.executeRawJet (decodedSource p D c source) := by
  have valid : ∀ q ∈ qs, q.z < D := by
    intro q hq
    exact ((SubexpExtractionJobs.mem_queries D q).mp (hqs.mem_iff.mp hq)).1
  rw [SubexpMomentArray.map_eq_range_contents,
    SubexpMomentPhase.fold_length, SubexpMomentPhase.zeroCells_length,
    contents_fold p D M c t z o ht hz ho slots hn hs source qs valid _
      (SubexpMomentPhase.zeroCells_length p D)]
  have hzCells : readCells (SubexpMomentPhase.zeroCells p D) = fun _ => 0 :=
    SubexpMomentArray.contents_replicate (decode p D c)
      (SubexpCoefficientLookup.zeroCoefficient p (D + 1)) (decode_zero p D c) D
  rw [hzCells]
  exact SubexpJetAccumulator.permuted_queries_fold_eq_rawJet
    (decodedSource p D c source) qs hqs

include ht hz ho hn hs in
theorem generated_fold_eq_rawJet :
    ((SubexpQueryOrder.generatedQueries D).foldl
      (SubexpMomentPhase.step p D M t z o slots source)
      (SubexpMomentPhase.zeroCells p D)).map (decode p D c) =
        Algorithm.executeRawJet (decodedSource p D c source) :=
  fold_eq_rawJet p D M c t z o ht hz ho slots hn hs source _
    (SubexpQueryOrder.generatedQueries_perm D)

include ht hz ho hn hs in
/-- The physical repeated-query schedule and the earlier represented jet
loop produce the same decoded coefficient list. This is the handoff to the
global-polynomial and CRT correctness theorems. -/
theorem fold_eq_executedJet (qs : List (Query D))
    (hqs : qs.Perm (SubexpExtractionJobs.queries D)) :
    (qs.foldl (SubexpMomentPhase.step p D M t z o slots source)
      (SubexpMomentPhase.zeroCells p D)).map (decode p D c) =
        (SubexpJetExecution.executeJet ops source).1.map (decode p D c) := by
  have h := SubexpJetExecution.executeJet_decode sem source
  exact (fold_eq_rawJet p D M c t z o ht hz ho slots hn hs source qs hqs).trans h.symm

end Prepared

/-- This specialization uses the slot and query orders emitted by the
actual generators. Their completeness and uniqueness are discharged. -/
theorem generated_visitSlots_eq_rawJet (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (c : Fin 4 → ZMod (p ^ (D + 1))) (t z o : QuarticCode p D)
    (ht : t.map (wordValue p (D + 1)) = reductionData c)
    (hz : quotientDenote c (z.map (wordValue p (D + 1))) = 0)
    (ho : quotientDenote c (o.map (wordValue p (D + 1))) = 1)
    (source : (Fin D → ℕ) → Algorithm.Expr (CoeffList D (QuarticCode p D))) :
    ((SubexpQueryOrder.generatedQueries D).foldl
      (SubexpMomentPhase.step p D M t z o (SubexpQueryOrder.visitSlots D) source)
      (SubexpMomentPhase.zeroCells p D)).map (decode p D c) =
        Algorithm.executeRawJet (decodedSource p D c source) :=
  generated_fold_eq_rawJet p D M c t z o ht hz ho (SubexpQueryOrder.visitSlots D)
    (SubexpQueryOrder.visitSlots_nodup D) (SubexpQueryOrder.mem_visitSlots D) source

end SubexponentialSAT.SubexpMomentSemantics

end OAI.Algorithms
