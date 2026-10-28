import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.QuarticSearch
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms

namespace OAI.Algorithms

/-!
# Synthetic quartic tests on binary coefficient words

The arithmetic uses only addition and multiplication, with a prepared word
for minus one. The zero tests are calls to existing fixed finite programs;
their costs count actual instructions and preserve all coefficient stacks.
-/
namespace SubexponentialSAT.SubexpQuarticTestProgram

open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

/-- Eight scalar calls: four multiplies and four additions. -/
def linearArithmetic {A : Type*} (add mul : A → A → A)
    (minusOne : A) (c : Fin 4 → A) (a : A) : A :=
  let na := mul a minusOne
  let b₂ := add (c 3) na
  let b₁ := add (c 2) (mul na b₂)
  let b₀ := add (c 1) (mul na b₁)
  add (c 0) (mul na b₀)

/-- Twelve scalar calls: six multiplies and six additions. -/
def quadraticArithmetic {A : Type*} (add mul : A → A → A)
    (minusOne : A) (c : Fin 4 → A) (a : Fin 2 → A) : Fin 2 → A :=
  let na₀ := mul (a 0) minusOne
  let na₁ := mul (a 1) minusOne
  let b₁ := add (c 3) na₁
  let b₀ := add (add (c 2) na₀) (mul na₁ b₁)
  let r₀ := add (c 0) (mul na₀ b₀)
  let r₁ := add (c 1) (add (mul na₁ b₀) (mul na₀ b₁))
  ![r₀, r₁]

theorem linearArithmetic_correct {R : Type*} [CommRing R]
    (c : Fin 4 → R) (a : R) :
    linearArithmetic (· + ·) (· * ·) (-1) c a =
      QuarticSearch.linearRemainder c a := by
  simp [linearArithmetic, QuarticSearch.linearRemainder, QuarticSearch.linearQuotient]
  ring

theorem quadraticArithmetic_correct {R : Type*} [CommRing R]
    (c : Fin 4 → R) (a : Fin 2 → R) :
    quadraticArithmetic (· + ·) (· * ·) (-1) c a =
      QuarticSearch.quadraticRemainder c a := by
  funext i
  fin_cases i <;>
    simp [quadraticArithmetic, QuarticSearch.quadraticRemainder,
      QuarticSearch.quadraticQuotient] <;> ring

section Words

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

/-- Prepared binary callbacks; the modulus and all words are runtime data. -/
def linearWord (minusOne : Word (baseWidth p μ))
    (c : Fin 4 → Word (baseWidth p μ)) (a : Word (baseWidth p μ)) :
    Word (baseWidth p μ) :=
  linearArithmetic (fun x y => (SubexpPreparedQuartic.wordAdd p μ M x y).1)
    (fun x y => (SubexpPreparedQuartic.wordMul p μ M x y).1) minusOne c a

def quadraticWord (minusOne : Word (baseWidth p μ))
    (c : Fin 4 → Word (baseWidth p μ)) (a : Fin 2 → Word (baseWidth p μ)) :
    Fin 2 → Word (baseWidth p μ) :=
  quadraticArithmetic (fun x y => (SubexpPreparedQuartic.wordAdd p μ M x y).1)
    (fun x y => (SubexpPreparedQuartic.wordMul p μ M x y).1) minusOne c a

theorem linearWord_value (minusOne : Word (baseWidth p μ))
    (c : Fin 4 → Word (baseWidth p μ)) (a : Word (baseWidth p μ))
    (hminus : wordValue p μ minusOne = -1) :
    wordValue p μ (linearWord p μ M minusOne c a) =
      QuarticSearch.linearRemainder (fun i => wordValue p μ (c i)) (wordValue p μ a) := by
  unfold linearWord linearArithmetic
  simp only [SubexpPreparedQuartic.wordAdd_correct,
    SubexpPreparedQuartic.wordMul_correct, hminus]
  exact linearArithmetic_correct (fun i => wordValue p μ (c i)) (wordValue p μ a)

theorem quadraticWord_value (minusOne : Word (baseWidth p μ))
    (c : Fin 4 → Word (baseWidth p μ)) (a : Fin 2 → Word (baseWidth p μ))
    (hminus : wordValue p μ minusOne = -1) (i : Fin 2) :
    wordValue p μ (quadraticWord p μ M minusOne c a i) =
      QuarticSearch.quadraticRemainder (fun i => wordValue p μ (c i))
        (fun i => wordValue p μ (a i)) i := by
  have h := congrFun (quadraticArithmetic_correct
    (fun i => wordValue p μ (c i)) (fun i => wordValue p μ (a i))) i
  fin_cases i <;>
    simpa [quadraticWord, quadraticArithmetic, SubexpPreparedQuartic.wordAdd_correct,
      SubexpPreparedQuartic.wordMul_correct, hminus] using h

theorem linearWord_canonical (minusOne : Word (baseWidth p μ))
    (c : Fin 4 → Word (baseWidth p μ)) (a : Word (baseWidth p μ)) :
    BinaryArithmetic.toNat (linearWord p μ M minusOne c a).val < p^μ :=
  SubexpPreparedQuartic.wordAdd_canonical p μ M _ _

theorem quadraticWord_canonical (minusOne : Word (baseWidth p μ))
    (c : Fin 4 → Word (baseWidth p μ)) (a : Fin 2 → Word (baseWidth p μ)) (i : Fin 2) :
    BinaryArithmetic.toNat (quadraticWord p μ M minusOne c a i).val < p^μ := by
  fin_cases i <;> exact SubexpPreparedQuartic.wordAdd_canonical p μ M _ _

end Words

section ZeroTests

variable {R S : ℕ}

/-- Canonical residue words are zero in the ring exactly when their bits encode zero. -/
theorem word_zero_iff (modulus : ℕ) (word : List Bool)
    (hcanonical : BinaryArithmetic.toNat word < modulus) :
    BinaryArithmetic.toNat word = 0 ↔ (BinaryArithmetic.toNat word : ZMod modulus) = 0 := by
  rw [← ZMod.val_eq_zero, ZMod.val_natCast_of_lt hcanonical]

theorem word_nonzero_iff (modulus : ℕ) (word : List Bool)
    (hcanonical : BinaryArithmetic.toNat word < modulus) :
    (Bool.not (CounterPrograms.isZero word)) = true ↔ (BinaryArithmetic.toNat word : ZMod modulus) ≠ 0 := by
  rw [Bool.not_eq_true_eq_eq_false, CounterPrograms.isZero_eq_false_iff,
    CounterPrograms.value_eq_toNat, Nat.pos_iff_ne_zero]
  exact not_congr (word_zero_iff modulus word hcanonical)

/-- An actual fixed-program call producing a residue-nonzero bit, preserving
all stacks. Scratch emptiness and canonical residue representation are explicit. -/
theorem residue_nonzero_eval (ports : CounterForPrograms.Ports R S)
    (d : StructuredCalls.State R S) (modulus : ℕ)
    (hscratch : d.stacks ports.scratch = [])
    (hcanonical : BinaryArithmetic.toNat (d.stacks ports.counter) < modulus) :
    ∃ out : StructuredCalls.State R S,
      StructuredCalls.Eval (CounterForPrograms.testCmd ports)
        (8 * (d.stacks ports.counter).length + 7) d out ∧
      out.stacks = d.stacks ∧
      (out.regs (ports.register 2) = true ↔
        (BinaryArithmetic.toNat (d.stacks ports.counter) : ZMod modulus) ≠ 0) := by
  refine ⟨CounterForPrograms.testResult ports d,
    CounterForPrograms.test_eval ports d hscratch,
    CounterForPrograms.testResult_stacks ports d hscratch, ?_⟩
  rw [CounterForPrograms.testResult_flag]
  exact word_nonzero_iff modulus _ hcanonical

/-- The residue test has a measured execution on the primitive bit machine. -/
theorem residue_nonzero_primitive (ports : CounterForPrograms.Ports R S)
    (d : StructuredCalls.State R S) (modulus : ℕ)
    (hscratch : d.stacks ports.scratch = [])
    (hcanonical : BinaryArithmetic.toNat (d.stacks ports.counter) < modulus) :
    let program := StructuredCalls.compiled (CounterForPrograms.testCmd ports)
      ports.counter ports.counter
    ∃ out : StructuredCalls.State R S,
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * (8 * (d.stacks ports.counter).length + 8))
        (primitiveCfg program (d.withPC (some program.entry)))
        (primitiveCfg program (out.withPC none)) ∧
      out.stacks = d.stacks ∧
      (out.regs (ports.register 2) = true ↔
        (BinaryArithmetic.toNat (d.stacks ports.counter) : ZMod modulus) ≠ 0) := by
  obtain ⟨out, he, hst, hv⟩ := residue_nonzero_eval ports d modulus hscratch hcanonical
  refine ⟨out, ?_, hst, hv⟩
  simpa only [Nat.add_assoc] using
    StructuredCalls.primitive_execution he ports.counter ports.counter

/-- Registers outside the three test ports survive the concrete nonzero call. -/
theorem nonzero_register_frame (ports : CounterForPrograms.Ports R S)
    (d : StructuredCalls.State R S) (j : Fin R)
    (hj : ∀ i : Fin 3, ports.register i ≠ j) :
    (CounterForPrograms.testResult ports d).regs j = d.regs j := by
  simp only [CounterForPrograms.testResult, Atom.eval, State.ofCfg,
    Atom.instr, execInstr]
  rw [Function.update_of_ne (Ne.symm (hj 2))]
  apply StructuredCalls.embedState_register_frame
  rintro ⟨i, hi⟩
  exact hj i hi

end ZeroTests

section PairTest

variable {S : ℕ}

def firstRegisters : Fin 3 ↪ Fin 8 := ⟨![0, 1, 2], by decide⟩
def secondRegisters : Fin 3 ↪ Fin 8 := ⟨![0, 1, 3], by decide⟩

def firstPorts (counter scratch : Fin S) (h : counter ≠ scratch) :
    CounterForPrograms.Ports 8 S := ⟨firstRegisters, counter, scratch, h⟩

def secondPorts (counter scratch : Fin S) (h : counter ≠ scratch) :
    CounterForPrograms.Ports 8 S := ⟨secondRegisters, counter, scratch, h⟩

/-- Test two canonical remainder words and OR their nonzero flags. -/
abbrev pairTestCmd (left right scratch : Fin S)
    (hl : left ≠ scratch) (hr : right ≠ scratch) : StructuredCalls.Cmd 8 S :=
  .seq (CounterForPrograms.testCmd (firstPorts left scratch hl))
    (.seq (CounterForPrograms.testCmd (secondPorts right scratch hr))
      (.base (.atom (.bor 2 2 3))))

noncomputable def pairTestResult (left right scratch : Fin S)
    (hl : left ≠ scratch) (hr : right ≠ scratch)
    (d : StructuredCalls.State 8 S) : StructuredCalls.State 8 S :=
  let d₀ := CounterForPrograms.testResult (firstPorts left scratch hl) d
  let d₁ := CounterForPrograms.testResult (secondPorts right scratch hr) d₀
  (Atom.bor 2 2 3).eval d₁

theorem pairTest_eval (left right scratch : Fin S)
    (hl : left ≠ scratch) (hr : right ≠ scratch)
    (d : StructuredCalls.State 8 S) (hs : d.stacks scratch = []) :
    StructuredCalls.Eval (pairTestCmd left right scratch hl hr)
      (8 * (d.stacks left).length + 8 * (d.stacks right).length + 15)
      d (pairTestResult left right scratch hl hr d) := by
  let p₀ := firstPorts left scratch hl
  let p₁ := secondPorts right scratch hr
  let d₀ := CounterForPrograms.testResult p₀ d
  have h₀ := CounterForPrograms.test_eval p₀ d hs
  have hs₀ : d₀.stacks = d.stacks := CounterForPrograms.testResult_stacks p₀ d hs
  have h₁ := CounterForPrograms.test_eval p₁ d₀ (by rw [hs₀]; exact hs)
  have hb := StructuredCalls.Eval.base (StructuredProgram.Eval.atom
    (Atom.bor 2 2 3) (CounterForPrograms.testResult p₁ d₀))
  have hall := h₀.seq (h₁.seq hb)
  dsimp only [p₀, p₁, d₀, firstPorts, secondPorts] at hall hs₀
  rw [hs₀] at hall
  have htime :
      (8 * (d.stacks left).length + 7) +
          (8 * (d.stacks right).length + 7 + 1) =
        8 * (d.stacks left).length + 8 * (d.stacks right).length + 15 := by
    omega
  rw [htime] at hall
  exact hall

theorem pairTest_stacks (left right scratch : Fin S)
    (hl : left ≠ scratch) (hr : right ≠ scratch)
    (d : StructuredCalls.State 8 S) (hs : d.stacks scratch = []) :
    (pairTestResult left right scratch hl hr d).stacks = d.stacks := by
  let d₀ := CounterForPrograms.testResult (firstPorts left scratch hl) d
  have h₀ : d₀.stacks = d.stacks :=
    CounterForPrograms.testResult_stacks (firstPorts left scratch hl) d hs
  have h₁ := CounterForPrograms.testResult_stacks (secondPorts right scratch hr) d₀
    (by rw [h₀]; exact hs)
  exact h₁.trans h₀

theorem pairTest_flag (left right scratch : Fin S)
    (hl : left ≠ scratch) (hr : right ≠ scratch)
    (d : StructuredCalls.State 8 S) (hs : d.stacks scratch = []) :
    (pairTestResult left right scratch hl hr d).regs 2 =
      (!(CounterPrograms.isZero (d.stacks left)) ||
        !(CounterPrograms.isZero (d.stacks right))) := by
  let p₀ := firstPorts left scratch hl
  let p₁ := secondPorts right scratch hr
  let d₀ := CounterForPrograms.testResult p₀ d
  let d₁ := CounterForPrograms.testResult p₁ d₀
  have hs₀ : d₀.stacks = d.stacks := CounterForPrograms.testResult_stacks p₀ d hs
  have hfirst : d₀.regs 2 = !(CounterPrograms.isZero (d.stacks left)) :=
    CounterForPrograms.testResult_flag p₀ d
  have hkeep : d₁.regs 2 = d₀.regs 2 := by
    apply nonzero_register_frame
    intro i
    fin_cases i
    all_goals norm_num [p₁, secondPorts, secondRegisters]
  have hsecond : d₁.regs 3 = !(CounterPrograms.isZero (d.stacks right)) := by
    have hh := CounterForPrograms.testResult_flag p₁ d₀
    change d₁.regs (p₁.register 2) = !(CounterPrograms.isZero (d.stacks right))
    simpa only [d₁, p₁, secondPorts, hs₀] using hh
  change (Function.update d₁.regs 2 (d₁.regs 2 || d₁.regs 3)) 2 = _
  simp only [Function.update_self, hkeep, hfirst, hsecond]

theorem pairTest_residue_iff (left right scratch : Fin S)
    (hl : left ≠ scratch) (hr : right ≠ scratch)
    (d : StructuredCalls.State 8 S) (hs : d.stacks scratch = []) (modulus : ℕ)
    (hleft : BinaryArithmetic.toNat (d.stacks left) < modulus) (hright : BinaryArithmetic.toNat (d.stacks right) < modulus) :
    (pairTestResult left right scratch hl hr d).regs 2 = true ↔
      ((BinaryArithmetic.toNat (d.stacks left) : ZMod modulus) ≠ 0 ∨
        (BinaryArithmetic.toNat (d.stacks right) : ZMod modulus) ≠ 0) := by
  rw [pairTest_flag left right scratch hl hr d hs, Bool.or_eq_true,
    word_nonzero_iff modulus _ hleft, word_nonzero_iff modulus _ hright]

theorem pairTest_primitive (left right scratch : Fin S)
    (hl : left ≠ scratch) (hr : right ≠ scratch)
    (d : StructuredCalls.State 8 S) (hs : d.stacks scratch = []) (modulus : ℕ)
    (hleft : BinaryArithmetic.toNat (d.stacks left) < modulus) (hright : BinaryArithmetic.toNat (d.stacks right) < modulus) :
    let program := StructuredCalls.compiled (pairTestCmd left right scratch hl hr) left left
    ∃ out : StructuredCalls.State 8 S,
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program *
          (8 * (d.stacks left).length + 8 * (d.stacks right).length + 16))
        (primitiveCfg program (d.withPC (some program.entry)))
        (primitiveCfg program (out.withPC none)) ∧
      out.stacks = d.stacks ∧
      (out.regs 2 = true ↔
        ((BinaryArithmetic.toNat (d.stacks left) : ZMod modulus) ≠ 0 ∨
          (BinaryArithmetic.toNat (d.stacks right) : ZMod modulus) ≠ 0)) := by
  refine ⟨pairTestResult left right scratch hl hr d, ?_,
    pairTest_stacks left right scratch hl hr d hs,
    pairTest_residue_iff left right scratch hl hr d hs modulus hleft hright⟩
  simpa only [Nat.add_assoc] using StructuredCalls.primitive_execution
    (pairTest_eval left right scratch hl hr d hs) left left

end PairTest

section Passes

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

def linearWordPass (minusOne : Word (baseWidth p μ))
    (c : Fin 4 → Word (baseWidth p μ)) (a : Word (baseWidth p μ)) : Bool :=
  !(CounterPrograms.isZero (linearWord p μ M minusOne c a).val)

def quadraticWordPass (minusOne : Word (baseWidth p μ))
    (c : Fin 4 → Word (baseWidth p μ)) (a : Fin 2 → Word (baseWidth p μ)) : Bool :=
  (!(CounterPrograms.isZero (quadraticWord p μ M minusOne c a 0).val)) ||
    (!(CounterPrograms.isZero (quadraticWord p μ M minusOne c a 1).val))

/-- The binary callback returns exactly the Boolean used by quartic search. -/
theorem linearWordPass_eq (minusOne : Word (baseWidth p μ))
    (c : Fin 4 → Word (baseWidth p μ)) (a : Word (baseWidth p μ))
    (hminus : wordValue p μ minusOne = -1) :
    linearWordPass p μ M minusOne c a =
      QuarticSearch.linearPass (p^μ) (fun i => wordValue p μ (c i)) (wordValue p μ a) := by
  apply Bool.eq_iff_iff.mpr
  rw [linearWordPass, word_nonzero_iff (p^μ) _ (linearWord_canonical p μ M _ _ _),
    QuarticSearch.linearPass, decide_eq_true_eq]
  change wordValue p μ (linearWord p μ M minusOne c a) ≠ 0 ↔ _
  rw [linearWord_value p μ M _ _ _ hminus]

theorem quadraticWordPass_eq (minusOne : Word (baseWidth p μ))
    (c : Fin 4 → Word (baseWidth p μ)) (a : Fin 2 → Word (baseWidth p μ))
    (hminus : wordValue p μ minusOne = -1) :
    quadraticWordPass p μ M minusOne c a =
      QuarticSearch.quadraticPass (p^μ)
        (fun i => wordValue p μ (c i)) (fun i => wordValue p μ (a i)) := by
  apply Bool.eq_iff_iff.mpr
  rw [quadraticWordPass, Bool.or_eq_true,
    word_nonzero_iff (p^μ) _ (quadraticWord_canonical p μ M _ _ _ 0),
    word_nonzero_iff (p^μ) _ (quadraticWord_canonical p μ M _ _ _ 1),
    QuarticSearch.quadraticPass, decide_eq_true_eq]
  change (wordValue p μ (quadraticWord p μ M minusOne c a 0) ≠ 0 ∨
    wordValue p μ (quadraticWord p μ M minusOne c a 1) ≠ 0) ↔ _
  rw [quadraticWord_value p μ M _ _ _ hminus,
    quadraticWord_value p μ M _ _ _ hminus]

end Passes

end SubexponentialSAT.SubexpQuarticTestProgram

end OAI.Algorithms
