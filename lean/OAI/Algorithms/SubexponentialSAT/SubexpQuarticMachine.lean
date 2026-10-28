import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.SubexpScalarMachine

namespace OAI.Algorithms

/-!
# Fixed stack programs for the quartic coefficient arithmetic

Persistent word registers are separate from the destructive scalar workspace.
Each instruction copies its two operands into that workspace, executes a scalar
program, and moves the answer back. One additional stack suffices for the copies.
-/

namespace SubexponentialSAT.SubexpQuarticMachine

open SubexponentialSAT.BitProgram SubexponentialSAT.StackRoutines SubexponentialSAT.ProgramLinking
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

inductive ScalarOp where
  | add | mul
  deriving DecidableEq

structure Instr (v : ℕ) where
  op : ScalarOp
  dst : Fin v
  lhs : Fin v
  rhs : Fin v
  deriving DecidableEq

def ScalarOp.eval (op : ScalarOp) (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ)
    (x y : Word (baseWidth p μ)) : Word (baseWidth p μ) :=
  match op with
  | .add => (SubexpPreparedQuartic.wordAdd p μ M x y).1
  | .mul => (SubexpPreparedQuartic.wordMul p μ M x y).1

def Instr.eval {v : ℕ} (i : Instr v) (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ)
    (bank : Fin v → Word (baseWidth p μ)) : Fin v → Word (baseWidth p μ) :=
  Function.update bank i.dst (i.op.eval p μ M (bank i.lhs) (bank i.rhs))

def scriptEval {v : ℕ} (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) :
    List (Instr v) → (Fin v → Word (baseWidth p μ)) → (Fin v → Word (baseWidth p μ))
  | [], bank => bank
  | i :: code, bank => scriptEval p μ M code (i.eval p μ M bank)

def bankPort {v : ℕ} (i : Fin v) : Fin (v + 9) := Fin.castAdd 9 i
def workPort (v : ℕ) (i : Fin 8) : Fin (v + 9) := Fin.natAdd v (Fin.castAdd 1 i)
def tempPort (v : ℕ) : Fin (v + 9) := Fin.natAdd v (Fin.natAdd 8 (0 : Fin 1))

@[simp] theorem bankPort_inj {v : ℕ} {i j : Fin v} :
    bankPort i = bankPort j ↔ i = j := Fin.castAdd_inj

@[simp] theorem workPort_inj {v : ℕ} {i j : Fin 8} :
    workPort v i = workPort v j ↔ i = j := by
  simp [workPort, Fin.ext_iff]

@[simp] theorem bankPort_ne_workPort {v : ℕ} (i : Fin v) (j : Fin 8) :
    bankPort i ≠ workPort v j := by
  intro h
  have := congrArg Fin.val h
  simp [bankPort, workPort] at this
  omega

@[simp] theorem workPort_ne_bankPort {v : ℕ} (i : Fin 8) (j : Fin v) :
    workPort v i ≠ bankPort j := (bankPort_ne_workPort j i).symm

@[simp] theorem bankPort_ne_tempPort {v : ℕ} (i : Fin v) :
    bankPort i ≠ tempPort v := by
  intro h
  have := congrArg Fin.val h
  simp [bankPort, tempPort] at this
  omega

@[simp] theorem tempPort_ne_bankPort {v : ℕ} (i : Fin v) :
    tempPort v ≠ bankPort i := (bankPort_ne_tempPort i).symm

@[simp] theorem workPort_ne_tempPort {v : ℕ} (i : Fin 8) :
    workPort v i ≠ tempPort v := by
  intro h
  have := congrArg Fin.val h
  simp [workPort, tempPort] at this
  omega

@[simp] theorem tempPort_ne_workPort {v : ℕ} (i : Fin 8) :
    tempPort v ≠ workPort v i := (workPort_ne_tempPort i).symm

/-- The bank, eight scalar stacks, and a single copying stack. -/
def store {v : ℕ} (bank : Fin v → List Bool) (work : Fin 8 → List Bool)
    (temp : List Bool) : Fin (v + 9) → List Bool :=
  fun i => Fin.addCases bank
    (fun j => Fin.addCases (motive := fun _ : Fin 9 => List Bool)
      work (fun _ : Fin 1 => temp) j) i

@[simp] theorem store_bank {v : ℕ} (bank : Fin v → List Bool)
    (work : Fin 8 → List Bool) (temp : List Bool) (i : Fin v) :
    store bank work temp (bankPort i) = bank i := by simp [store, bankPort]

@[simp] theorem store_work {v : ℕ} (bank : Fin v → List Bool)
    (work : Fin 8 → List Bool) (temp : List Bool) (i : Fin 8) :
    store bank work temp (workPort v i) = work i := by simp [store, workPort]

@[simp] theorem store_temp {v : ℕ} (bank : Fin v → List Bool)
    (work : Fin 8 → List Bool) (temp : List Bool) :
    store bank work temp (tempPort v) = temp := by
  simp only [store, tempPort, Fin.addCases_right]

theorem store_ext {v : ℕ} {s t : Fin (v + 9) → List Bool}
    (hb : ∀ i, s (bankPort i) = t (bankPort i))
    (hw : ∀ i, s (workPort v i) = t (workPort v i))
    (ht : s (tempPort v) = t (tempPort v)) : s = t := by
  funext i
  refine Fin.addCases (fun j => hb j) (fun j => ?_) i
  refine Fin.addCases (m := 8) (n := 1) (motive := fun k : Fin 9 =>
    s (Fin.natAdd v k) = t (Fin.natAdd v k)) (fun k => hw k) (fun k => ?_) j
  fin_cases k
  exact ht

theorem store_update_bank {v : ℕ} (bank : Fin v → List Bool)
    (work : Fin 8 → List Bool) (temp xs : List Bool) (i : Fin v) :
    Function.update (store bank work temp) (bankPort i) xs =
      store (Function.update bank i xs) work temp := by
  apply store_ext <;> simp [Function.update_apply]

theorem store_update_work {v : ℕ} (bank : Fin v → List Bool)
    (work : Fin 8 → List Bool) (temp xs : List Bool) (i : Fin 8) :
    Function.update (store bank work temp) (workPort v i) xs =
      store bank (Function.update work i xs) temp := by
  apply store_ext <;> simp [Function.update_apply]

theorem store_update_temp {v : ℕ} (bank : Fin v → List Bool)
    (work : Fin 8 → List Bool) (temp xs : List Bool) :
    Function.update (store bank work temp) (tempPort v) xs = store bank work xs := by
  apply store_ext <;> simp []

abbrev scalarWork (x y modulus : List Bool) : Fin 8 → List Bool :=
  ModularRingPrograms.extendSeven (ModularRingPrograms.scalarInput x y modulus) []

@[simp] theorem scalarWork_zero (x y modulus : List Bool) :
    scalarWork x y modulus 0 = x := rfl
@[simp] theorem scalarWork_one (x y modulus : List Bool) :
    scalarWork x y modulus 1 = y := rfl

@[simp] theorem scalarWork_update_zero (x y modulus z : List Bool) :
    Function.update (scalarWork x y modulus) 0 z = scalarWork z y modulus := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem scalarWork_update_one (x y modulus z : List Bool) :
    Function.update (scalarWork x y modulus) 1 z = scalarWork x z modulus := by
  funext i
  fin_cases i <;> rfl

def restingState {v B : ℕ} (regs : Fin 8 → Bool) (bank : Fin v → Word B)
    (modulus : List Bool) : StructuredCalls.State 8 (v + 9) :=
  ⟨regs, store (fun i => (bank i).val) (scalarWork [] [] modulus) []⟩

@[simp] theorem restingState_bank {v B : ℕ} (regs : Fin 8 → Bool)
    (bank : Fin v → Word B) (modulus : List Bool) (i : Fin v) :
    (restingState regs bank modulus).stacks (bankPort i) = (bank i).val := by
  simp [restingState]

@[simp] theorem restingState_modulus {v B : ℕ} (regs : Fin 8 → Bool)
    (bank : Fin v → Word B) (modulus : List Bool) :
    (restingState regs bank modulus).stacks (workPort v 5) = modulus := by
  simp [restingState, scalarWork, ModularRingPrograms.extendSeven,
    ModularRingPrograms.scalarInput,
    ModularDivisionPrograms.seven]

@[simp] theorem restingState_temp {v B : ℕ} (regs : Fin 8 → Bool)
    (bank : Fin v → Word B) (modulus : List Bool) :
    (restingState regs bank modulus).stacks (tempPort v) = [] := by
  simp [restingState]

theorem restingState_scratch {v B : ℕ} (regs : Fin 8 → Bool)
    (bank : Fin v → Word B) (modulus : List Bool) (i : Fin 8) (hi : i ≠ 5) :
    (restingState regs bank modulus).stacks (workPort v i) = [] := by
  fin_cases i <;> simp_all [restingState, scalarWork,
    ModularRingPrograms.extendSeven, ModularRingPrograms.scalarInput, ModularDivisionPrograms.seven]

theorem embed_work {v : ℕ} (regs frameRegs : Fin 8 → Bool)
    (bank : Fin v → List Bool) (work frameWork : Fin 8 → List Bool) (temp : List Bool) :
    StructuredCalls.embedState id (workPort v) ⟨frameRegs, store bank frameWork temp⟩
        ⟨regs, work⟩ = ⟨regs, store bank work temp⟩ := by
  have ext : ∀ (a b : StructuredCalls.State 8 (v + 9)),
      a.regs = b.regs → a.stacks = b.stacks → a = b := by
    rintro ⟨ar, ast⟩ ⟨br, bst⟩ hr hs
    cases hr
    cases hs
    rfl
  apply ext
  · simp [StructuredCalls.embedState]
  · apply store_ext
    · intro i
      rw [StructuredCalls.embedState_stack_frame]
      · simp
      · rintro ⟨j, h⟩
        exact workPort_ne_bankPort j i h
    · intro i
      rw [StructuredCalls.embedState_stack]
      · simp
      · intro a b h
        exact workPort_inj.mp h
    · rw [StructuredCalls.embedState_stack_frame]
      · simp
      · rintro ⟨j, h⟩
        exact workPort_ne_tempPort j h

def resetRegs (regs : Fin 8 → Bool) : Fin 8 → Bool := readRegs regs 0 1 none

@[simp] theorem resetRegs_reset (regs : Fin 8 → Bool) :
    resetRegs (resetRegs regs) = resetRegs regs := readRegs_reset _ _ _ _

def dataState {v : ℕ} (regs : Fin 8 → Bool) (bank : Fin v → List Bool)
    (work : Fin 8 → List Bool) (temp : List Bool) : StructuredCalls.State 8 (v + 9) :=
  ⟨regs, store bank work temp⟩

abbrev copyInCmd {v : ℕ} (src : Fin v) (dst : Fin 8) : StructuredCalls.Cmd 8 (v + 9) :=
  .call (copyProgram (bankPort src) (workPort v dst) (tempPort v) 0 1)

theorem scalarCall_eval {v l n : ℕ} (p : Program 8 8 l)
    (regs finalRegs : Fin 8 → Bool) (bank : Fin v → List Bool)
    (input output : Fin 8 → List Bool)
    (ht : Trace p n ⟨some p.entry, regs, input⟩ ⟨none, finalRegs, output⟩) :
    StructuredCalls.Eval (.call (liftProgram p id (workPort v))) n
      (dataState regs bank input []) (dataState finalRegs bank output []) := by
  have h := StructuredCalls.eval_call_lifted p id (workPort v)
    (dataState regs bank input []) Function.injective_id
    (fun _ _ h => workPort_inj.mp h)
    (a := ⟨regs, input⟩) (b := ⟨finalRegs, output⟩) (n := n) ht
  simpa only [dataState, embed_work] using h

theorem copyIn_eval {v : ℕ} (src : Fin v) (dst : Fin 8)
    (regs : Fin 8 → Bool) (bank : Fin v → List Bool) (work : Fin 8 → List Bool)
    (hdst : work dst = []) :
    StructuredCalls.Eval (copyInCmd src dst) (7 * (bank src).length + 5)
      (dataState regs bank work [])
      (dataState (resetRegs regs) bank (Function.update work dst (bank src)) []) := by
  have ht := ListRegisterProgram.copy_run (bankPort src) (workPort v dst) (tempPort v)
    (0 : Fin 8) 1 (by simp) (by simp) (by simp) (by decide)
    regs (store bank work []) (by simp)
  have hs : copyStacks (bankPort src) (workPort v dst) (store bank work []) =
      store bank (Function.update work dst (bank src)) [] := by
    simp [copyStacks, hdst, store_update_work]
  apply StructuredCalls.Eval.call
  simpa [ListRegisterProgram.Run, dataState, StructuredProgram.State.withPC,
    resetRegs, hs] using ht

abbrev returnCmd {v : ℕ} (dst : Fin v) : StructuredCalls.Cmd 8 (v + 9) :=
  .seq (.call (clearProgram (bankPort dst) 0 1))
    (.seq (.call (transferProgram (workPort v 0) (tempPort v) 0 1))
      (.call (transferProgram (tempPort v) (bankPort dst) 0 1)))

theorem return_eval {v : ℕ} (dst : Fin v) (regs : Fin 8 → Bool)
    (bank : Fin v → List Bool) (work : Fin 8 → List Bool) :
    StructuredCalls.Eval (returnCmd dst)
      (2 * (bank dst).length + 3 +
        ((3 * (work 0).length + 3) + (3 * (work 0).length + 3)))
      (dataState regs bank work [])
      (dataState (resetRegs regs) (Function.update bank dst (work 0))
        (Function.update work 0 []) []) := by
  let b := Function.update bank dst []
  let w := Function.update work 0 []
  have h1 := ListRegisterProgram.clear_run (bankPort dst) (0 : Fin 8) 1
    regs (store bank work [])
  have h1s : clearStacks (bankPort dst) (store bank work []) = store b work [] := by
    simp [clearStacks, b, store_update_bank]
  have e1 : StructuredCalls.Eval (.call (clearProgram (bankPort dst) 0 1))
      (2 * (bank dst).length + 3) (dataState regs bank work [])
      (dataState (resetRegs regs) b work []) := by
    apply StructuredCalls.Eval.call
    simpa [ListRegisterProgram.Run, dataState, StructuredProgram.State.withPC,
      resetRegs, h1s] using h1
  have h2 := ListRegisterProgram.transfer_run (workPort v 0) (tempPort v) (0 : Fin 8) 1
    (by simp) (by decide) (resetRegs regs) (store b work [])
  have h2s : transferStacks (workPort v 0) (tempPort v) (store b work []) =
      store b w (work 0).reverse := by
    simp [transferStacks, w, store_update_work, store_update_temp]
  have e2 : StructuredCalls.Eval
      (.call (transferProgram (workPort v 0) (tempPort v) 0 1))
      (3 * (work 0).length + 3) (dataState (resetRegs regs) b work [])
      (dataState (resetRegs regs) b w (work 0).reverse) := by
    apply StructuredCalls.Eval.call
    simpa [ListRegisterProgram.Run, dataState, StructuredProgram.State.withPC,
      resetRegs, readRegs_reset, h2s] using h2
  have h3 := ListRegisterProgram.transfer_run (tempPort v) (bankPort dst) (0 : Fin 8) 1
    (by simp) (by decide) (resetRegs regs) (store b w (work 0).reverse)
  have h3s : transferStacks (tempPort v) (bankPort dst) (store b w (work 0).reverse) =
      store (Function.update bank dst (work 0)) w [] := by
    simp [transferStacks, b, store_update_temp, store_update_bank]
  have e3 : StructuredCalls.Eval
      (.call (transferProgram (tempPort v) (bankPort dst) 0 1))
      (3 * (work 0).length + 3) (dataState (resetRegs regs) b w (work 0).reverse)
      (dataState (resetRegs regs) (Function.update bank dst (work 0)) w []) := by
    apply StructuredCalls.Eval.call
    simpa [ListRegisterProgram.Run, dataState, StructuredProgram.State.withPC,
      resetRegs, readRegs_reset, h3s] using h3
  exact StructuredCalls.Eval.seq e1 (StructuredCalls.Eval.seq e2 e3)

abbrev ScalarOp.labels : ScalarOp → ℕ
  | .add => 136
  | .mul => 141

abbrev ScalarOp.program (op : ScalarOp) : Program 8 8 op.labels :=
  match op with
  | .add => ModularRingPrograms.wordAddProgram
  | .mul => ModularRingPrograms.wordMulProgram

theorem ScalarOp.run (op : ScalarOp) (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (regs : Fin 8 → Bool)
    (x y : Word (baseWidth p μ)) :
    ∃ (finalRegs : Fin 8 → Bool) (n : ℕ), n ≤ 6000 * (baseWidth p μ + 1)^2 ∧
      Trace op.program n
        ⟨some op.program.entry, regs, scalarWork x.val y.val M.bits⟩
        ⟨none, finalRegs, scalarWork (op.eval p μ M x y).val [] M.bits⟩ := by
  cases op with
  | add =>
      obtain ⟨rf, n, hn, ht⟩ := SubexpScalarMachine.wordAdd_run p μ M regs x y
      refine ⟨rf, n, hn, ?_⟩
      simpa only [ScalarOp.program, ScalarOp.eval, scalarWork,
        ModularRingPrograms.extendSeven, ModularRingPrograms.scalarInput,
        ModularDivisionPrograms.resting, ModularDivisionPrograms.seven] using ht
  | mul =>
      obtain ⟨rf, n, hn, ht⟩ := SubexpScalarMachine.wordMul_run p μ M regs x y
      refine ⟨rf, n, hn, ?_⟩
      simpa only [ScalarOp.program, ScalarOp.eval, scalarWork,
        ModularRingPrograms.extendSeven, ModularRingPrograms.scalarInput,
        ModularDivisionPrograms.resting, ModularDivisionPrograms.seven] using ht

abbrev instrCmd {v : ℕ} (i : Instr v) : StructuredCalls.Cmd 8 (v + 9) :=
  .seq (copyInCmd i.lhs 0)
    (.seq (copyInCmd i.rhs 1)
      (.seq (.call (liftProgram i.op.program id (workPort v))) (returnCmd i.dst)))

def scriptCmd {v : ℕ} : List (Instr v) → StructuredCalls.Cmd 8 (v + 9)
  | [] => .base .skip
  | i :: code => .seq (instrCmd i) (scriptCmd code)

private theorem instruction_cost_bound (B n : ℕ) (hn : n ≤ 6000 * (B + 1)^2) :
    (7 * B + 5) + ((7 * B + 5) +
      (n + (2 * B + 3 + ((3 * B + 3) + (3 * B + 3))))) ≤ 6100 * (B + 1)^2 := by
  have hsq := Nat.le_mul_self (B + 1)
  rw [← pow_two] at hsq
  omega

private theorem halt_cost_bound (B C n : ℕ) (hn : n ≤ C * (B + 1)^2) :
    n + 1 ≤ (C + 1) * (B + 1)^2 := by
  have hsq := Nat.le_mul_self (B + 1)
  rw [← pow_two] at hsq
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem instr_run {v : ℕ} (i : Instr v) (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (regs : Fin 8 → Bool)
    (bank : Fin v → Word (baseWidth p μ)) :
    ∃ (n : ℕ) (finalRegs : Fin 8 → Bool), n ≤ 6100 * (baseWidth p μ + 1)^2 ∧
      StructuredCalls.Eval (instrCmd i) n (restingState regs bank M.bits)
        (restingState finalRegs (i.eval p μ M bank) M.bits) := by
  let b : Fin v → List Bool := fun j => (bank j).val
  let x := bank i.lhs
  let y := bank i.rhs
  let z := i.op.eval p μ M x y
  obtain ⟨rf, n, hn, ht⟩ := i.op.run p μ M (resetRegs regs) x y
  have e1 := copyIn_eval i.lhs 0 regs b (scalarWork [] [] M.bits) rfl
  have e2 := copyIn_eval i.rhs 1 (resetRegs regs) b (scalarWork x.val [] M.bits) rfl
  simp only [scalarWork_update_zero] at e1
  simp only [scalarWork_update_one, resetRegs_reset] at e2
  have e3 := scalarCall_eval i.op.program (resetRegs regs) rf b
    (scalarWork x.val y.val M.bits) (scalarWork z.val [] M.bits) ht
  have e4 := return_eval i.dst rf b (scalarWork z.val [] M.bits)
  simp only [scalarWork_zero, scalarWork_update_zero] at e4
  have he := StructuredCalls.Eval.seq e1
    (StructuredCalls.Eval.seq e2 (StructuredCalls.Eval.seq e3 e4))
  have hbank : Function.update b i.dst z.val =
      fun j => (i.eval p μ M bank j).val := by
    funext j
    by_cases hj : j = i.dst
    · subst j
      simp only [Instr.eval, Function.update_self, z, x, y]
    · simp [Instr.eval, b, z, x, y, hj]
  refine ⟨(7 * baseWidth p μ + 5) + ((7 * baseWidth p μ + 5) +
    (n + (2 * baseWidth p μ + 3 +
      ((3 * baseWidth p μ + 3) + (3 * baseWidth p μ + 3))))),
    resetRegs rf, ?_, ?_⟩
  · exact instruction_cost_bound _ _ hn
  · simpa only [instrCmd, restingState, dataState, hbank,
      b, x, y, z, (bank i.lhs).property, (bank i.rhs).property,
      (bank i.dst).property, (i.op.eval p μ M (bank i.lhs) (bank i.rhs)).property] using he

theorem script_run {v : ℕ} (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (code : List (Instr v))
    (regs : Fin 8 → Bool) (bank : Fin v → Word (baseWidth p μ)) :
    ∃ (n : ℕ) (finalRegs : Fin 8 → Bool),
      n ≤ code.length * 6100 * (baseWidth p μ + 1)^2 ∧
      StructuredCalls.Eval (scriptCmd code) n (restingState regs bank M.bits)
        (restingState finalRegs (scriptEval p μ M code bank) M.bits) := by
  induction code generalizing regs bank with
  | nil =>
      exact ⟨0, regs, by simp, StructuredCalls.Eval.base (StructuredProgram.Eval.skip _)⟩
  | cons i code ih =>
      obtain ⟨n, r1, hn, he⟩ := instr_run i p μ M regs bank
      obtain ⟨m, r2, hm, hf⟩ := ih r1 (i.eval p μ M bank)
      refine ⟨n + m, r2, ?_, StructuredCalls.Eval.seq he hf⟩
      simp only [List.length_cons, Nat.add_mul]
      omega

/-- Four scalar additions, retaining both input quartics. -/
def addCode : List (Instr 12) :=
  [⟨.add, 8, 0, 4⟩, ⟨.add, 9, 1, 5⟩,
   ⟨.add, 10, 2, 6⟩, ⟨.add, 11, 3, 7⟩]

/-- The literal 49-operation Horner circuit from `SubexpQuarticRing.mulRun`.
Slots 0--3 hold the reduction coefficients, 4--7 the left operand, and
8--11 the right operand. Every scalar result has its own persistent slot. -/
def mulCode : List (Instr 61) :=
  [⟨.mul, 12, 7, 8⟩, ⟨.mul, 13, 7, 9⟩,
   ⟨.mul, 14, 7, 10⟩, ⟨.mul, 15, 7, 11⟩,
   ⟨.mul, 16, 15, 0⟩, ⟨.mul, 17, 15, 1⟩,
   ⟨.mul, 18, 15, 2⟩, ⟨.mul, 19, 15, 3⟩,
   ⟨.add, 20, 12, 17⟩, ⟨.add, 21, 13, 18⟩, ⟨.add, 22, 14, 19⟩,
   ⟨.mul, 23, 6, 8⟩, ⟨.mul, 24, 6, 9⟩,
   ⟨.mul, 25, 6, 10⟩, ⟨.mul, 26, 6, 11⟩,
   ⟨.add, 27, 23, 16⟩, ⟨.add, 28, 24, 20⟩,
   ⟨.add, 29, 25, 21⟩, ⟨.add, 30, 26, 22⟩,
   ⟨.mul, 31, 30, 0⟩, ⟨.mul, 32, 30, 1⟩,
   ⟨.mul, 33, 30, 2⟩, ⟨.mul, 34, 30, 3⟩,
   ⟨.add, 35, 27, 32⟩, ⟨.add, 36, 28, 33⟩, ⟨.add, 37, 29, 34⟩,
   ⟨.mul, 38, 5, 8⟩, ⟨.mul, 39, 5, 9⟩,
   ⟨.mul, 40, 5, 10⟩, ⟨.mul, 41, 5, 11⟩,
   ⟨.add, 42, 38, 31⟩, ⟨.add, 43, 39, 35⟩,
   ⟨.add, 44, 40, 36⟩, ⟨.add, 45, 41, 37⟩,
   ⟨.mul, 46, 45, 0⟩, ⟨.mul, 47, 45, 1⟩,
   ⟨.mul, 48, 45, 2⟩, ⟨.mul, 49, 45, 3⟩,
   ⟨.add, 50, 42, 47⟩, ⟨.add, 51, 43, 48⟩, ⟨.add, 52, 44, 49⟩,
   ⟨.mul, 53, 4, 8⟩, ⟨.mul, 54, 4, 9⟩,
   ⟨.mul, 55, 4, 10⟩, ⟨.mul, 56, 4, 11⟩,
   ⟨.add, 57, 53, 46⟩, ⟨.add, 58, 54, 50⟩,
   ⟨.add, 59, 55, 51⟩, ⟨.add, 60, 56, 52⟩]

@[simp] theorem addCode_length : addCode.length = 4 := rfl
@[simp] theorem mulCode_length : mulCode.length = 49 := rfl

def addLeft {A : Type*} (bank : Fin 12 → A) : Quad A :=
  ⟨bank 0, bank 1, bank 2, bank 3⟩
def addRight {A : Type*} (bank : Fin 12 → A) : Quad A :=
  ⟨bank 4, bank 5, bank 6, bank 7⟩
def addOutput {A : Type*} (bank : Fin 12 → A) : Quad A :=
  ⟨bank 8, bank 9, bank 10, bank 11⟩

def mulReduction {A : Type*} (bank : Fin 61 → A) : Quad A :=
  ⟨bank 0, bank 1, bank 2, bank 3⟩
def mulLeft {A : Type*} (bank : Fin 61 → A) : Quad A :=
  ⟨bank 4, bank 5, bank 6, bank 7⟩
def mulRight {A : Type*} (bank : Fin 61 → A) : Quad A :=
  ⟨bank 8, bank 9, bank 10, bank 11⟩
def mulOutput {A : Type*} (bank : Fin 61 → A) : Quad A :=
  ⟨bank 57, bank 58, bank 59, bank 60⟩

theorem addCode_correct (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (bank : Fin 12 → Word (baseWidth p μ)) :
    addOutput (scriptEval p μ M addCode bank) =
      (SubexpPreparedQuartic.binaryAdd p μ M (addLeft bank) (addRight bank)).1 := by
  rfl

theorem mulCode_correct (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (bank : Fin 61 → Word (baseWidth p μ)) :
    mulOutput (scriptEval p μ M mulCode bank) =
      (SubexpPreparedQuartic.binaryMul p μ M
        (mulReduction bank) (mulLeft bank) (mulRight bank)).1 := by
  rfl

theorem scriptEval_frame {v : ℕ} (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (code : List (Instr v))
    (bank : Fin v → Word (baseWidth p μ)) (j : Fin v)
    (hj : ∀ i ∈ code, i.dst ≠ j) : scriptEval p μ M code bank j = bank j := by
  induction code generalizing bank with
  | nil => rfl
  | cons i code ih =>
      rw [scriptEval, ih]
      · exact Function.update_of_ne (hj i (by simp)).symm _ _
      · intro k hk
        exact hj k (by simp [hk])

theorem addCode_preserves_inputs (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (bank : Fin 12 → Word (baseWidth p μ))
    (j : Fin 12) (hj : j.val < 8) : scriptEval p μ M addCode bank j = bank j := by
  apply scriptEval_frame
  have hd : ∀ i ∈ addCode, 8 ≤ i.dst.val := by norm_num [addCode, Fin.coe_ofNat_eq_mod]
  intro i hi he
  have := hd i hi
  rw [he] at this
  omega

theorem mulCode_preserves_inputs (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (bank : Fin 61 → Word (baseWidth p μ))
    (j : Fin 61) (hj : j.val < 12) : scriptEval p μ M mulCode bank j = bank j := by
  apply scriptEval_frame
  have hd : ∀ i ∈ mulCode, 12 ≤ i.dst.val := by norm_num [mulCode, Fin.coe_ofNat_eq_mod]
  intro i hi he
  have := hd i hi
  rw [he] at this
  omega

theorem addProgram_size : StructuredCalls.size (scriptCmd addCode) + 1 = 653 := rfl
theorem mulProgram_size : StructuredCalls.size (scriptCmd mulCode) + 1 = 8128 := rfl

def addProgram : Program 8 21 (StructuredCalls.size (scriptCmd addCode) + 1) :=
  StructuredCalls.compiled (scriptCmd addCode) (bankPort 0) (bankPort 8)

def mulProgram : Program 8 70 (StructuredCalls.size (scriptCmd mulCode) + 1) :=
  StructuredCalls.compiled (scriptCmd mulCode) (bankPort 0) (bankPort 57)

/-- Fixed absolute constants: neither the program nor its primitive simulation
overhead depends on the prime, exponent, or input words. -/
noncomputable def addConstant : ℕ := primitiveOverhead addProgram * (4 * 6100 + 1)
noncomputable def mulConstant : ℕ := primitiveOverhead mulProgram * (49 * 6100 + 1)
theorem add_run (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (regs : Fin 8 → Bool) (bank : Fin 12 → Word (baseWidth p μ)) :
    ∃ (n : ℕ) (finalRegs : Fin 8 → Bool), n ≤ 4 * 6100 * (baseWidth p μ + 1)^2 ∧
      StructuredCalls.Eval (scriptCmd addCode) n (restingState regs bank M.bits)
        (restingState finalRegs (scriptEval p μ M addCode bank) M.bits) := by
  simpa only [addCode_length] using script_run p μ M addCode regs bank

theorem mul_run (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (regs : Fin 8 → Bool) (bank : Fin 61 → Word (baseWidth p μ)) :
    ∃ (n : ℕ) (finalRegs : Fin 8 → Bool), n ≤ 49 * 6100 * (baseWidth p μ + 1)^2 ∧
      StructuredCalls.Eval (scriptCmd mulCode) n (restingState regs bank M.bits)
        (restingState finalRegs (scriptEval p μ M mulCode bank) M.bits) := by
  simpa only [mulCode_length] using script_run p μ M mulCode regs bank

theorem add_program_run (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (regs : Fin 8 → Bool)
    (bank : Fin 12 → Word (baseWidth p μ)) :
    ∃ finalRegs,
      RunsIn addProgram ((4 * 6100 + 1) * (baseWidth p μ + 1)^2)
        ((restingState regs bank M.bits).withPC (some addProgram.entry))
        ((restingState finalRegs (scriptEval p μ M addCode bank) M.bits).withPC none) := by
  obtain ⟨n, rf, hn, he⟩ := add_run p μ M regs bank
  refine ⟨rf, n + 1, ?_, StructuredCalls.compiled_halt_trace he _ _⟩
  exact halt_cost_bound _ _ _ hn

theorem mul_program_run (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (regs : Fin 8 → Bool)
    (bank : Fin 61 → Word (baseWidth p μ)) :
    ∃ finalRegs,
      RunsIn mulProgram ((49 * 6100 + 1) * (baseWidth p μ + 1)^2)
        ((restingState regs bank M.bits).withPC (some mulProgram.entry))
        ((restingState finalRegs (scriptEval p μ M mulCode bank) M.bits).withPC none) := by
  obtain ⟨n, rf, hn, he⟩ := mul_run p μ M regs bank
  refine ⟨rf, n + 1, ?_, StructuredCalls.compiled_halt_trace he _ _⟩
  exact halt_cost_bound _ _ _ hn

theorem add_program_terminates (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (regs : Fin 8 → Bool)
    (bank : Fin 12 → Word (baseWidth p μ)) :
    ∃ finalState,
      RunsIn addProgram ((4 * 6100 + 1) * (baseWidth p μ + 1)^2)
        ((restingState regs bank M.bits).withPC (some addProgram.entry))
        finalState := by
  obtain ⟨rf, ht⟩ := add_program_run p μ M regs bank
  exact ⟨_, ht⟩

theorem add_primitive {n : ℕ}
    {a b : Cfg 8 21 (StructuredCalls.size (scriptCmd addCode) + 1)}
    (h : RunsIn addProgram n a b) :
    Computation.RunsIn (primitive addProgram).step (primitiveOverhead addProgram * n)
      (primitiveCfg addProgram a) (primitiveCfg addProgram b) :=
  BitProgram.primitive_execution addProgram h

end SubexponentialSAT.SubexpQuarticMachine

end OAI.Algorithms
