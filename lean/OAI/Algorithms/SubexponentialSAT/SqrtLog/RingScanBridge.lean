import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanTripleLoop
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramFold

namespace OAI.Algorithms

/-! Exact byte interfaces between the semantic ring callbacks and fixed native
flat-stack scanners. Materializing the input vectors/triples is a separate,
explicitly charged caller operation. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

private theorem leftBits_map {B : ℕ} (pairs : List (Word B × Word B)) :
    leftBits pairs = (pairs.map fun x => x.1.val).flatten := by
  induction pairs with
  | nil => rfl
  | cons x xs ih => simp only [leftBits, List.map_cons, List.flatten_cons, ih]

private theorem rightBits_map {B : ℕ} (pairs : List (Word B × Word B)) :
    rightBits pairs = (pairs.map fun x => x.2.val).flatten := by
  induction pairs with
  | nil => rfl
  | cons x xs ih => simp only [rightBits, List.map_cons, List.flatten_cons, ih]

private theorem sumBits_map (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (pairs : List (Word (baseWidth p t) × Word (baseWidth p t))) :
    sumBits p t M pairs =
      (pairs.map fun x => (SubexpPreparedQuartic.wordAdd p t M x.1 x.2).1.val).flatten := by
  induction pairs with
  | nil => rfl
  | cons x xs ih => simp only [sumBits, List.map_cons, List.flatten_cons, ih]

/-- The flat input/output of the native scanner is precisely the semantic
coefficient-vector add callback, including exact canonical result words. -/
theorem addRun_native (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (x y : RingProgram.Code (Word (baseWidth p t)) d)
    (regs : Fin 8 → Bool) (count width : List Bool)
    (hcount : count.length = d) (hwidth : width.length = baseWidth p t) :
    ∃ finalRegs, RunsIn addVectorProgram
      (d * (6000 * (baseWidth p t + 1)^2 + 34 * baseWidth p t + 29) + 6)
      ((addState regs M.bits [] [] (RingProgram.flat x) (RingProgram.flat y) [] count width).withPC
        (some addVectorProgram.entry))
      ((addState finalRegs M.bits
        (RingProgram.flat (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1)
        [] [] [] [] [] width).withPC none) := by
  obtain ⟨rf, hrun⟩ := addVectorProgram_run p t M
    (List.ofFn fun i : Fin d => (x i, y i)) regs count width
    (by simpa using hcount) hwidth
  refine ⟨rf, ?_⟩
  simp only [List.length_ofFn, leftBits_map, rightBits_map, sumBits_map,
    List.map_ofFn] at hrun
  simpa only [Function.comp_def, Prod.fst, Prod.snd, RingProgram.flat,
    RingProgram.addRun, RingProgram.tabulateRun_eq, RingProgram.scalarProgram] using hrun

theorem prepared_wordAdd_comm (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (a b : Word (baseWidth p t)) :
    (SubexpPreparedQuartic.wordAdd p t M a b).1 =
      (SubexpPreparedQuartic.wordAdd p t M b a).1 := by
  apply RingProgram.word_eq_of_value p t
  · exact SubexpPreparedQuartic.wordAdd_canonical p t M a b
  · exact SubexpPreparedQuartic.wordAdd_canonical p t M b a
  · simp only [SubexpPreparedQuartic.wordAdd_correct, add_comm]

theorem foldTriples_eq_accumulate (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (triples : List (WordTriple (baseWidth p t))) (seed : Word (baseWidth p t)) :
    foldTriples p t M seed triples =
      (RingProgram.accumulateTriplesRun (RingProgram.scalarProgram p t M cache) triples seed).1 := by
  induction triples generalizing seed with
  | nil => rfl
  | cons x xs ih =>
      change foldTriples p t M
        (SubexpPreparedQuartic.wordAdd p t M (tripleProduct p t M x.1 x.2.1 x.2.2) seed).1 xs =
        (RingProgram.accumulateTriplesRun (RingProgram.scalarProgram p t M cache) xs
          (SubexpPreparedQuartic.wordAdd p t M seed (tripleProduct p t M x.1 x.2.1 x.2.2)).1).1
      rw [prepared_wordAdd_comm p t M]
      exact ih _

/-- Each physical streamed coordinate is exactly the original right-fold
coefficient callback. The canonical-zero hypothesis is discharged by the
prepared scalar-cache construction. -/
theorem coordinateMulRun_native (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (x y : RingProgram.Code (Word (baseWidth p t)) d) (k : Fin d)
    (regs : Fin 8 → Bool) (count width suffix : List Bool)
    (hcount : count.length = d*d) (hwidth : width.length = baseWidth p t) :
    ∃ finalRegs, RunsIn tripleScanProgram
      (d*d * (18000 * (baseWidth p t + 1)^2 + 48 * baseWidth p t + 44) + 3)
      ((addState regs M.bits cache.zero.val [] []
        (tripleBits (RingProgram.coordinateTriples table x y k) ++ suffix) [] count width).withPC
        (some tripleScanProgram.entry))
      ((addState finalRegs M.bits
        (RingProgram.coordinateMulRun (RingProgram.scalarProgram p t M cache) table x y k).1.val
        [] [] suffix [] [] width).withPC none) := by
  obtain ⟨rf, hrun⟩ := tripleScanProgram_run_suffix p t M
    (RingProgram.coordinateTriples table x y k) cache.zero regs count width suffix
    (by simpa using hcount) hwidth
  refine ⟨rf, ?_⟩
  rw [foldTriples_eq_accumulate p t M cache,
    RingProgram.accumulateTriplesRun_eq_dot p t M cache _ hz,
    ← RingProgram.coordinateMulRun_eq_dot] at hrun
  simpa only [RingProgram.coordinateTriples_length] using hrun

/-- Primitive-machine refinement of the same physical vector-add execution. -/
theorem addVectorProgram_primitive (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t)
    (pairs : List (Word (baseWidth p t) × Word (baseWidth p t)))
    (regs : Fin 8 → Bool) (count width : List Bool)
    (hcount : count.length = pairs.length) (hwidth : width.length = baseWidth p t) :
    ∃ finalRegs,
      Computation.RunsIn (primitive addVectorProgram).step
        (primitiveOverhead addVectorProgram *
          (pairs.length * (6000 * (baseWidth p t + 1)^2 + 34 * baseWidth p t + 29) + 6))
        (primitiveCfg addVectorProgram
          ((addState regs M.bits [] [] (leftBits pairs) (rightBits pairs) [] count width).withPC
            (some addVectorProgram.entry)))
        (primitiveCfg addVectorProgram
          ((addState finalRegs M.bits (sumBits p t M pairs) [] [] [] [] [] width).withPC none)) := by
  obtain ⟨rf, hr⟩ := addVectorProgram_run p t M pairs regs count width hcount hwidth
  exact ⟨rf, BitProgram.primitive_execution _ hr⟩

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
