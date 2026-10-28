import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramAlgebra
import OAI.Algorithms.SubexponentialSAT.SubexpScalarMachine

namespace OAI.Algorithms

/-! Fixed-width base-ring words for arbitrary extension degree. The arithmetic
programs below are the audited fixed scalar programs; the degree does not occur
in their instruction tables. Extension-vector scanning is a separate layer. -/
namespace SubexponentialSAT.SqrtLog.RingProgram

open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.BitProgram SubexponentialSAT.ModularRingPrograms SubexponentialSAT.ModularDivisionPrograms

variable (p t : ℕ) [Fact p.Prime]

abbrev ScalarCode := Word (baseWidth p t)

structure ScalarCache where
  zero : ScalarCode p t
  one : ScalarCode p t
  minusOne : ScalarCode p t
  zero_correct : wordValue p t zero = 0
  one_correct : wordValue p t one = 1
  minusOne_correct : wordValue p t minusOne = -1

variable (M : SubexpPreparedQuartic.Modulus p t)

/-- The cache is computed using literal-word preparation and modular negation.
Its correctness proofs do not enter the executable data. -/
def prepareScalarCache (ht : 0 < t) : ScalarCache p t × ℕ :=
  let z := SubexpPreparedQuartic.literalWordRun p t []
  let o := SubexpPreparedQuartic.literalWordRun p t [true]
  let m := SubexpPreparedQuartic.wordNeg p t M o.1
  (⟨z.1, o.1, m.1, SubexpPreparedQuartic.literalWordRun_zero p t,
    SubexpPreparedQuartic.literalWordRun_one p t ht, by
      rw [SubexpPreparedQuartic.wordNeg_correct, SubexpPreparedQuartic.literalWordRun_one p t ht]⟩,
    z.2 + o.2 + m.2)

theorem prepareScalarCache_cost (ht : 0 < t) :
    (prepareScalarCache p t M ht).2 ≤ 2 * (3 * baseWidth p t + 1) + scalarBudget p t := by
  have hn := SubexpPreparedQuartic.wordNeg_cost p t M
    (SubexpPreparedQuartic.literalWordRun p t [true]).1
  simp only [prepareScalarCache, SubexpPreparedQuartic.literalWordRun_cost]
  omega

def scalarProgram (cache : ScalarCache p t) : RingProgram (ScalarCode p t) where
  zeroRun := (cache.zero, baseWidth p t)
  oneRun := (cache.one, baseWidth p t)
  addRun := SubexpPreparedQuartic.wordAdd p t M
  mulRun := SubexpPreparedQuartic.wordMul p t M
  negRun x := SubexpPreparedQuartic.wordMul p t M x cache.minusOne

def scalarRing (cache : ScalarCache p t) : RepresentedRing (ScalarCode p t) (ZMod (p^t)) where
  decode := wordValue p t
  zeroRun := (cache.zero, baseWidth p t)
  oneRun := (cache.one, baseWidth p t)
  addRun := SubexpPreparedQuartic.wordAdd p t M
  mulRun := SubexpPreparedQuartic.wordMul p t M
  negRun x := SubexpPreparedQuartic.wordMul p t M x cache.minusOne
  zero_correct := cache.zero_correct
  one_correct := cache.one_correct
  add_correct := SubexpPreparedQuartic.wordAdd_correct p t M
  mul_correct := SubexpPreparedQuartic.wordMul_correct p t M
  neg_correct x := by
    rw [SubexpPreparedQuartic.wordMul_correct, cache.minusOne_correct, mul_neg_one]

@[simp] theorem scalarRing_program (cache : ScalarCache p t) :
    (scalarRing p t M cache).program = scalarProgram p t M cache := rfl

theorem scalarRing_budget (cache : ScalarCache p t) :
    ScalarBudget (scalarRing p t M cache) (scalarBudget p t) := by
  have hb : baseWidth p t ≤ scalarBudget p t := by unfold scalarBudget; omega
  constructor
  · exact hb
  · exact hb
  · exact SubexpPreparedQuartic.wordAdd_cost p t M
  · exact SubexpPreparedQuartic.wordMul_cost p t M
  · intro x; exact SubexpPreparedQuartic.wordMul_cost p t M x cache.minusOne

/-- Exact byte refinement, including normalization, for the base addition. -/
theorem scalar_add_run (cache : ScalarCache p t) (regs : Fin 8 → Bool)
    (x y : ScalarCode p t) :
    ∃ finalRegs,
      RunsIn wordAddProgram (6000 * (baseWidth p t + 1)^2)
        ⟨some 0, regs, extendSeven (scalarInput x.val y.val M.bits) []⟩
        ⟨none, finalRegs, extendSeven
          (resting ((scalarProgram p t M cache).addRun x y).1.val M.bits []) []⟩ :=
  SubexponentialSAT.SubexpScalarMachine.wordAdd_run p t M regs x y

/-- Exact byte refinement, including normalization, for the base product. -/
theorem scalar_mul_run (cache : ScalarCache p t) (regs : Fin 8 → Bool)
    (x y : ScalarCode p t) :
    ∃ finalRegs,
      RunsIn wordMulProgram (6000 * (baseWidth p t + 1)^2)
        ⟨some 0, regs, extendSeven (scalarInput x.val y.val M.bits) []⟩
        ⟨none, finalRegs, extendSeven
          (resting ((scalarProgram p t M cache).mulRun x y).1.val M.bits []) []⟩ :=
  SubexponentialSAT.SubexpScalarMachine.wordMul_run p t M regs x y

/-- Negation is the same fixed multiplier with a cached minus-one operand. -/
theorem scalar_neg_run (cache : ScalarCache p t) (regs : Fin 8 → Bool)
    (x : ScalarCode p t) :
    ∃ finalRegs,
      RunsIn wordMulProgram (6000 * (baseWidth p t + 1)^2)
        ⟨some 0, regs, extendSeven (scalarInput x.val cache.minusOne.val M.bits) []⟩
        ⟨none, finalRegs, extendSeven
          (resting ((scalarProgram p t M cache).negRun x).1.val M.bits []) []⟩ :=
  SubexponentialSAT.SubexpScalarMachine.wordMul_run p t M regs x cache.minusOne

/-- Flat coefficient-vector ABI: coefficient zero first, each word little endian. -/
def flat {d B : ℕ} (x : Code (Word B) d) : List Bool :=
  (List.ofFn fun i => (x i).val).flatten

@[simp] theorem flat_length {d B : ℕ} (x : Code (Word B) d) :
    (flat x).length = d * B := by
  simp only [flat, List.length_flatten, List.map_ofFn, List.sum_ofFn]
  calc
    ∑ i : Fin d, (x i).val.length = ∑ _ : Fin d, B :=
      Finset.sum_congr rfl (fun i _ => (x i).property)
    _ = d * B := by simp

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
