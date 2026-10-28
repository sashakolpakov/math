import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedSetupBounds
import OAI.Algorithms.SubexponentialSAT.CounterNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.SubexpModulusMachine
import OAI.Algorithms.SubexponentialSAT.SubexpConstantPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticMarshal
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic

namespace OAI.Algorithms

/-!
# Runtime modulus and literal caches for the selected quartic ring

All commands below are fixed finite programs. The prime and precision enter as
binary words. The prime is physically trimmed before its width is used. Cache
indices 0 through 8 mean prime, precision, selected coefficients, modulus,
width shape, reduction coefficients, zero quartet, one quartet, and minus one.
-/

namespace SubexponentialSAT.SubexpPreparedQuarticPrelude

open BitProgram StructuredCalls SubexpPreparedSetupCalls BinaryArithmetic SubexpLiftRing

def primeWord (p : ℕ) := fixedBits (Nat.log 2 p + 1) p
def modulusWord (p μ : ℕ) := fixedBits (baseWidth p μ + 1) (p ^ μ)
def widthWord (p μ : ℕ) := (modulusWord p μ).tail
def literalWord (B : ℕ) (one : Bool) := fixedBits B (bitVal one)
def literalQuartet (B : ℕ) (one : Bool) :=
  literalWord B one ++ List.replicate (3 * B) false

@[simp] theorem primeWord_length (p : ℕ) : (primeWord p).length = Nat.log 2 p + 1 :=
  fixedBits_length _ _
@[simp] theorem primeWord_value (p : ℕ) : BinaryArithmetic.toNat (primeWord p) = p :=
  toNat_fixedBits_of_lt _ _ (Nat.lt_pow_succ_log_self Nat.one_lt_two p)
@[simp] theorem modulusWord_length (p μ : ℕ) : (modulusWord p μ).length = baseWidth p μ + 1 :=
  fixedBits_length _ _
@[simp] theorem widthWord_length (p μ : ℕ) : (widthWord p μ).length = baseWidth p μ := by
  simp [widthWord]
@[simp] theorem literalWord_length (B : ℕ) (one : Bool) : (literalWord B one).length = B :=
  fixedBits_length _ _
@[simp] theorem literalQuartet_length (B : ℕ) (one : Bool) : (literalQuartet B one).length = 4 * B := by
  simp [literalQuartet]
  omega

def Step (c : Command) (a : Data) (W N : ℕ) (dst : Cache) (value : List Bool) : Prop :=
  ∃ n b, Eval c n a b ∧ n ≤ N ∧ StackBound b W ∧
    cacheWords b = Function.update (cacheWords a) dst value

def trimPrime : Command :=
  stage CounterNormalizeProgram.program (by decide) (by decide) [(0, 0)] [(0, 0)]
def prepareModulus : Command :=
  stage SubexpModulusMachine.program (by decide) (by decide) [(0, 0), (1, 1)] [(10, 3)]

abbrev tailCommand : Cmd 2 1 := .base (.atom (.pop 0 0 1))
def tailProgram := compiled tailCommand 0 0
def tailState (r : Fin 2 → Bool) (bits : List Bool) : StructuredProgram.State 2 1 :=
  ⟨r, fun _ => bits⟩
def tailResult (bits : List Bool) :=
  StructuredProgram.Atom.eval (.pop (0 : Fin 1) 0 1) (tailState (fun _ => false) bits)

theorem tail_runs (bits : List Bool) :
    RunsIn tailProgram 2
      ((tailState (fun _ => false) bits).withPC (some tailProgram.entry))
      ((tailResult bits).withPC none) := by
  exact ⟨2, le_rfl, compiled_halt_trace
    (.base (StructuredProgram.Eval.atom (.pop (0 : Fin 1) 0 1)
      (tailState (fun _ => false) bits))) 0 0⟩

@[simp] theorem tailResult_stack (bits : List Bool) (i : Fin 1) :
    (tailResult bits).stacks i = bits.tail := by
  fin_cases i
  cases bits <;> simp [tailResult, tailState, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]

def prepareWidth : Command := stage tailProgram (by decide) (by decide) [(3, 0)] [(0, 4)]
def prepareLiteral (one : Bool) (dst : Cache) : Command :=
  stage (SubexpConstantPrograms.program one) (by decide) (by decide) [(4, 0)] [(0, dst)]
def marshalLiteral (dst : Cache) : Command :=
  stage SubexpQuarticMarshal.program (by decide) (by decide) [(dst, 0), (4, 1)] [(0, dst)]

theorem trimPrime_step (a : Data) (W p : ℕ) (ha : StackBound a W)
    (hp : 0 < p) (hv : BinaryArithmetic.toNat (cacheWords a 0) = p) (hb : Nat.log 2 p + 1 ≤ W) :
    Step trimPrime a W (9 * (cacheWords a 0).length + 21 + 200 * (W + 1)) 0 (primeWord p) := by
  let bits := cacheWords a 0
  let start := CounterNormalizeProgram.state (fun _ => false) bits []
  let out := CounterNormalizeProgram.state CounterNormalizeProgram.zeroRegs (primeWord p) []
  have hpos : 0 < CounterPrograms.value bits := by
    rw [CounterPrograms.value_eq_toNat]
    rw [hv]
    exact hp
  have ht := CounterNormalizeProgram.normalize_runs (fun _ => false) bits hpos
  have hval : CounterPrograms.value bits = p := by
    rw [CounterPrograms.value_eq_toNat]
    exact hv
  simp only [hval, Nat.log2_eq_log_two] at ht
  have hl : SubexpSetupStorage.project (registers (by decide : 3 ≤ 9))
      (work (by decide : 3 ≤ 24)) (prepared (by decide : 3 ≤ 24) [(0, 0)] a) = start := by
    apply prepared_eq _ _ _ _ _ (by decide) (by intro j; rfl)
    · intro q hq
      simp only [List.mem_singleton] at hq
      subst q
      rfl
    · intro j hj
      have h0 := hj (0, 0) (by simp)
      fin_cases j <;> simp_all [start, CounterNormalizeProgram.state]
  have ho : StackBound out W := by
    intro i
    fin_cases i <;> simp [out, CounterNormalizeProgram.state, primeWord_length]
    omega
  exact run_one CounterNormalizeProgram.program (by decide) (by decide) [(0, 0)] 0 0 a
    start out ha (by decide) (by decide) ho hl ht

theorem prepareModulus_step (a : Data) (W p μ : ℕ) (ha : StackBound a W)
    (hp : cacheWords a 0 = primeWord p) (hv : BinaryArithmetic.toNat (primeWord p) = p)
    (hμ : BinaryArithmetic.toNat (cacheWords a 1) = μ) (hB : baseWidth p μ + 1 ≤ W) :
    Step prepareModulus a W
      (SubexpModulusMachine.runtimeBound (primeWord p) (cacheWords a 1) + 200 * (W + 1))
      3 (modulusWord p μ) := by
  let bits := cacheWords a 1
  obtain ⟨rf, remaining, copied, hrem, hlrem, hcop, hlcop, ht⟩ :=
    SubexpModulusMachine.run_powerRun (fun _ => false) (primeWord p) bits
  rw [hμ, SubexpModulusConstruction.modulus_eq_fixedBits p μ (primeWord p) hv
    (primeWord_length p)] at ht
  let start := SubexpModulusMachine.state (fun _ => false) (primeWord p) bits [] [] []
  let out := SubexpModulusMachine.state rf (primeWord p) remaining [] copied (modulusWord p μ)
  have hl : SubexpSetupStorage.project (registers (by decide : 8 ≤ 9))
      (work (by decide : 11 ≤ 24)) (prepared (by decide : 11 ≤ 24) [(0, 0), (1, 1)] a) = start := by
    apply prepared_eq _ _ _ _ _ (by decide) (by intro j; rfl)
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact hp.symm
      · rfl
    · intro j hj
      have h0 := hj (0, 0) (by simp)
      have h1 := hj (1, 1) (by simp)
      fin_cases j <;> simp_all [start, SubexpModulusMachine.state, SubexpModulusMachine.stackState]
  have hb : Nat.log 2 p + 1 ≤ W := by
    have h := ha (cache 0)
    change (cacheWords a 0).length ≤ W at h
    simpa only [hp, primeWord_length] using h
  have he : bits.length ≤ W := ha (cache 1)
  have ho : StackBound out W := by
    intro i
    fin_cases i <;>
      simp [out, SubexpModulusMachine.state, SubexpModulusMachine.stackState,
        modulusWord_length] <;> omega
  exact run_one SubexpModulusMachine.program (by decide) (by decide) [(0, 0), (1, 1)] 10 3 a
    start out ha (by decide) (by decide) ho hl ht

theorem prepareWidth_step (a : Data) (W : ℕ) (ha : StackBound a W) :
    Step prepareWidth a W (2 + 200 * (W + 1)) 4 (cacheWords a 3).tail := by
  let bits := cacheWords a 3
  have hl : SubexpSetupStorage.project (registers (by decide : 2 ≤ 9))
      (work (by decide : 1 ≤ 24)) (prepared (by decide : 1 ≤ 24) [(3, 0)] a) =
      tailState (fun _ => false) bits := by
    apply prepared_eq _ _ _ _ _ (by decide) (by intro j; rfl)
    · intro q hq
      simp only [List.mem_singleton] at hq
      subst q
      rfl
    · intro j hj
      have h0 := hj (3, 0) (by simp)
      fin_cases j
      exact False.elim (h0 rfl)
  have ho : StackBound (tailResult bits) W := by
    intro i
    rw [tailResult_stack]
    rw [List.length_tail]
    exact (Nat.sub_le _ _).trans (ha (cache 3))
  simpa only [Step, prepareWidth, bits, tailResult_stack] using
    run_one tailProgram (by decide) (by decide) [(3, 0)] 0 4 a
      (tailState (fun _ => false) bits) (tailResult bits) ha (by decide) (by decide) ho hl (tail_runs bits)

theorem prepareLiteral_step (one : Bool) (dst : Cache) (a : Data) (W B : ℕ)
    (ha : StackBound a W) (hw : (cacheWords a 4).length = B)
    (hpos : one = true → 0 < B) :
    Step (prepareLiteral one dst) a W (7 * B + 9 + 200 * (W + 1)) dst (literalWord B one) := by
  let shape := cacheWords a 4
  obtain ⟨rf, ht⟩ := SubexpConstantPrograms.run_constant one (fun _ => false) shape (by
    intro hone; rw [hw]; exact hpos hone)
  rw [hw] at ht
  let start := SubexpConstantPrograms.state (fun _ => false) shape []
  let out := SubexpConstantPrograms.state rf (literalWord B one) []
  have hl : SubexpSetupStorage.project (registers (by decide : 8 ≤ 9))
      (work (by decide : 3 ≤ 24)) (prepared (by decide : 3 ≤ 24) [(4, 0)] a) = start := by
    apply prepared_eq _ _ _ _ _ (by decide) (by intro j; rfl)
    · intro q hq
      simp only [List.mem_singleton] at hq
      subst q
      rfl
    · intro j hj
      have h0 := hj (4, 0) (by simp)
      fin_cases j <;> simp_all [start, SubexpConstantPrograms.state, ModularPrograms.operandStacks]
  have hB : B ≤ W := by
    have h := ha (cache 4)
    change (cacheWords a 4).length ≤ W at h
    simpa only [hw] using h
  have ho : StackBound out W := by
    intro i
    fin_cases i <;>
      simp [out, SubexpConstantPrograms.state, ModularPrograms.operandStacks]
    omega
  exact run_one (SubexpConstantPrograms.program one) (by decide) (by decide) [(4, 0)] 0 dst a
    start out ha (by decide) (by decide) ho hl ht

theorem marshalLiteral_step (dst : Cache) (a : Data) (W B : ℕ)
    (ha : StackBound a W) (hw : (cacheWords a 4).length = B)
    (hd : (cacheWords a dst).length = B) (h4B : 4 * B ≤ W) :
    Step (marshalLiteral dst) a W (20 * B + 30 + 200 * (W + 1)) dst
      (cacheWords a dst ++ List.replicate (3 * B) false) := by
  let shape := cacheWords a 4
  let word := cacheWords a dst
  obtain ⟨rf, ht⟩ := SubexpQuarticMarshal.run_bound (fun _ => false) word shape B hd hw
  let start : StructuredProgram.State 3 5 :=
    ⟨fun _ => false, SubexpQuarticMarshal.stackState word shape [] [] []⟩
  let out : StructuredProgram.State 3 5 :=
    ⟨rf, SubexpQuarticMarshal.stackState (SubexpQuarticMarshal.marshalBits word shape) shape [] [] []⟩
  have hl : SubexpSetupStorage.project (registers (by decide : 3 ≤ 9))
      (work (by decide : 5 ≤ 24)) (prepared (by decide : 5 ≤ 24) [(dst, 0), (4, 1)] a) = start := by
    apply prepared_eq _ _ _ _ _ (by simp) (by intro j; rfl)
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> rfl
    · intro j hj
      have h0 := hj (dst, 0) (by simp)
      have h1 := hj (4, 1) (by simp)
      fin_cases j <;> simp_all [start, SubexpQuarticMarshal.stackState]
  have hshape : shape.length ≤ W := ha (cache 4)
  have hflat : (SubexpQuarticMarshal.marshalBits word shape).length ≤ W := by
    rw [SubexpQuarticMarshal.marshalBits_length word shape B hd hw]
    exact h4B
  have ho : StackBound out W := by
    intro i
    fin_cases i <;> simp [out, SubexpQuarticMarshal.stackState] <;> omega
  simpa only [Step, marshalLiteral, out, SubexpQuarticMarshal.stackState,
    Matrix.cons_val_zero, SubexpQuarticMarshal.marshalBits, shape, word, hw] using
    run_one SubexpQuarticMarshal.program (by decide) (by decide) [(dst, 0), (4, 1)] 0 dst a
      start out ha (by simp) (by simp) ho hl ht

def command : Command :=
  .seq trimPrime (.seq prepareModulus (.seq prepareWidth
    (.seq (prepareLiteral false 6) (.seq (marshalLiteral 6)
      (.seq (prepareLiteral true 7) (marshalLiteral 7))))))

def resultWords (old : Cache → List Bool) (p μ : ℕ) : Cache → List Bool :=
  Function.update
    (Function.update
      (Function.update
        (Function.update (Function.update old 0 (primeWord p)) 3 (modulusWord p μ))
        4 (widthWord p μ))
      6 (literalQuartet (baseWidth p μ) false))
    7 (literalQuartet (baseWidth p μ) true)

def runtimeBound (p μ W : ℕ) (prime precision : List Bool) : ℕ :=
  9 * prime.length + SubexpModulusMachine.runtimeBound (primeWord p) precision +
    54 * baseWidth p μ + 101 + 1400 * (W + 1)

/-- The prime input may contain arbitrarily many high zeroes. Precision is a
runtime binary word; no natural-number exponentiation is executed by `command`. -/
theorem command_run (a : Data) (W p μ : ℕ) (ha : StackBound a W)
    (hp : 0 < p) (hμ : 0 < μ)
    (hv : BinaryArithmetic.toNat (cacheWords a 0) = p) (he : BinaryArithmetic.toNat (cacheWords a 1) = μ)
    (hb : Nat.log 2 p + 1 ≤ W) (hB : baseWidth p μ + 1 ≤ W)
    (h4B : 4 * baseWidth p μ ≤ W) :
    ∃ n b, Eval command n a b ∧
      n ≤ runtimeBound p μ W (cacheWords a 0) (cacheWords a 1) ∧
      StackBound b W ∧ cacheWords b = resultWords (cacheWords a) p μ := by
  obtain ⟨n1, a1, e1, b1, w1, c1⟩ := trimPrime_step a W p ha hp hv hb
  have p1 : cacheWords a1 0 = primeWord p := by rw [c1]; simp
  have x1 : cacheWords a1 1 = cacheWords a 1 := by rw [c1]; simp
  obtain ⟨n2, a2, e2, b2, w2, c2⟩ := prepareModulus_step a1 W p μ w1 p1
    (primeWord_value p) (by rw [x1]; exact he) hB
  rw [x1] at b2
  have m2 : cacheWords a2 3 = modulusWord p μ := by rw [c2]; simp
  obtain ⟨n3, a3, e3, b3, w3, c3⟩ := prepareWidth_step a2 W w2
  have s3 : cacheWords a3 4 = widthWord p μ := by rw [c3]; simp [m2, widthWord]
  have l3 : (cacheWords a3 4).length = baseWidth p μ := by rw [s3, widthWord_length]
  obtain ⟨n4, a4, e4, b4, w4, c4⟩ :=
    prepareLiteral_step false 6 a3 W (baseWidth p μ) w3 l3 (by simp)
  have s4 : (cacheWords a4 4).length = baseWidth p μ := by rw [c4]; simpa using l3
  have l4 : (cacheWords a4 6).length = baseWidth p μ := by rw [c4]; simp
  obtain ⟨n5, a5, e5, b5, w5, c5⟩ :=
    marshalLiteral_step 6 a4 W (baseWidth p μ) w4 s4 l4 h4B
  have s5 : (cacheWords a5 4).length = baseWidth p μ := by rw [c5]; simpa using s4
  have bpos : 0 < baseWidth p μ := Nat.mul_pos hμ (Nat.zero_lt_succ _)
  obtain ⟨n6, a6, e6, b6, w6, c6⟩ :=
    prepareLiteral_step true 7 a5 W (baseWidth p μ) w5 s5 (by intro _; exact bpos)
  have s6 : (cacheWords a6 4).length = baseWidth p μ := by rw [c6]; simpa using s5
  have l6 : (cacheWords a6 7).length = baseWidth p μ := by rw [c6]; simp
  obtain ⟨n7, a7, e7, b7, w7, c7⟩ :=
    marshalLiteral_step 7 a6 W (baseWidth p μ) w6 s6 l6 h4B
  refine ⟨n1 + (n2 + (n3 + (n4 + (n5 + (n6 + n7))))), a7,
    e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7))))), ?_, w7, ?_⟩
  · unfold runtimeBound
    omega
  · funext i
    fin_cases i <;>
      simp [c7, c6, c5, c4, c3, c2, c1, resultWords, widthWord, literalQuartet]

end SubexponentialSAT.SubexpPreparedQuarticPrelude

end OAI.Algorithms
