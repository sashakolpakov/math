import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanContractLoop
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanBridge

namespace OAI.Algorithms

/-! Whole-vector native multiplication after explicitly paid triple expansion. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- The required source format groups the triple stream by output coordinate,
then by the two operand indices. Producing it is a separate paid program. -/
def multiplicationBlocks {d B : ℕ} (table : Fin d → Fin d → Fin d → Word B)
    (x y : RingProgram.Code (Word B) d) : List (List (WordTriple B)) :=
  List.ofFn fun k : Fin d => RingProgram.coordinateTriples table x y k

@[simp] theorem multiplicationBlocks_length {d B : ℕ}
    (table : Fin d → Fin d → Fin d → Word B) (x y : RingProgram.Code (Word B) d) :
    (multiplicationBlocks table x y).length = d := by simp [multiplicationBlocks]

theorem multiplicationBlocks_uniform {d B : ℕ}
    (table : Fin d → Fin d → Fin d → Word B) (x y : RingProgram.Code (Word B) d)
    (b : List (WordTriple B)) (hb : b ∈ multiplicationBlocks table x y) : b.length = d*d := by
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hb
  exact RingProgram.coordinateTriples_length table x y k

private theorem contractBits_map (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (seed : Word (baseWidth p t))
    (blocks : List (List (WordTriple (baseWidth p t)))) :
    contractBits p t M seed blocks =
      (blocks.map fun b => (foldTriples p t M seed b).val).flatten := by
  induction blocks with
  | nil => rfl
  | cons b bs ih => simp only [contractBits, List.map_cons, List.flatten_cons, ih]

theorem contractBits_mulRun (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (x y : RingProgram.Code (Word (baseWidth p t)) d) :
    contractBits p t M cache.zero (multiplicationBlocks table x y) =
      RingProgram.flat (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1 := by
  simp only [contractBits_map, multiplicationBlocks, List.map_ofFn,
    RingProgram.flat, RingProgram.mulRun, RingProgram.tabulateRun_eq]
  congr 2
  funext k
  dsimp only [Function.comp_apply]
  rw [foldTriples_eq_accumulate p t M cache,
    RingProgram.accumulateTriplesRun_eq_dot p t M cache _ hz,
    ← RingProgram.coordinateMulRun_eq_dot]

/-- A fixed native instruction table computes the complete bilinear product
from a k-major triple stream. All contraction work is charged. The input
format does not claim that generating the stream or table is free. -/
theorem mulRun_contract_native (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (x y : RingProgram.Code (Word (baseWidth p t)) d)
    (regs : Fin 8 → Bool) (width suffix outer inner : List Bool)
    (ho : outer.length = d) (hi : inner.length = d*d) (hw : width.length = baseWidth p t) :
    ∃ rf, RunsIn contractVectorProgram
      (d * (d*d * (18000 * (baseWidth p t + 1)^2 + 48 * baseWidth p t + 51)
        + 13 * baseWidth p t + 18) + 6)
      ((contractState regs M.bits [] (blockBits (multiplicationBlocks table x y) ++ suffix)
        [] width outer inner cache.zero.val []).withPC (some contractVectorProgram.entry))
      ((contractState rf M.bits
        (RingProgram.flat (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table x y).1)
        suffix [] width [] inner cache.zero.val []).withPC none) := by
  obtain ⟨rf, hr⟩ := contractVectorProgram_run p t M (multiplicationBlocks table x y)
    cache.zero regs width suffix outer inner (by simpa using ho)
    (fun b hb => hi.trans (multiplicationBlocks_uniform table x y b hb).symm) hw
  refine ⟨rf, ?_⟩
  simpa only [multiplicationBlocks_length, hi, contractBits_mulRun p t M cache hz] using hr

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
