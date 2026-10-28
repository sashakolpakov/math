import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StackRoutines
import OAI.Algorithms.SubexponentialSAT.ProgramLinking
import OAI.Algorithms.SubexponentialSAT.BitProgramCompile
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-!
# Unbounded Boolean-list registers implemented by finite programs

Logical words are Boolean stacks.  Three fixed scratch stacks suffice for
alias-safe word assignment, prefixing, and appending; all are restored empty.
The programs below contain only the existing finite Boolean/stack instructions.
Every stated cost is proved by an actual execution trace.
-/

namespace SubexponentialSAT.ListRegisterProgram

open BitProgram StackRoutines ProgramLinking

/-- A complete execution retaining an arbitrary surrounding data store. -/
abbrev Run {r s l : ℕ} (p : Program r s l) (n : ℕ)
    (regs : Fin r → Bool) (stk : Stacks (Fin s))
    (regs' : Fin r → Bool) (stk' : Stacks (Fin s)) : Prop :=
  Trace p n ⟨some p.entry, regs, stk⟩ ⟨none, regs', stk'⟩

theorem link_run {r s l m : ℕ} (p : Program r s l) (q : Program r s m)
    {n₁ n₂ : ℕ} {regs₀ regs₁ regs₂ : Fin r → Bool}
    {stk₀ stk₁ stk₂ : Stacks (Fin s)}
    (hp : Run p n₁ regs₀ stk₀ regs₁ stk₁)
    (hq : Run q n₂ regs₁ stk₁ regs₂ stk₂) :
    Run (link p q) (n₁ + n₂) regs₀ stk₀ regs₂ stk₂ := by
  simpa only [Run, relabelCfg, relocatePc, enter, link, linkInto] using
    link_trace p q hp rfl hq

theorem clear_run {r s : ℕ} (src : Fin s) (value present : Fin r)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Run (clearProgram src value present) (2 * (stk src).length + 3)
      regs stk (readRegs regs value present none) (clearStacks src stk) := by
  have h := halt_after_trace _ (clearProgram_trace src value present regs stk) 2 rfl rfl
  simpa [Run, clearProgram, clearResult, Nat.add_assoc] using h

theorem transfer_run {r s : ℕ} (src dst : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Run (transferProgram src dst value present) (3 * (stk src).length + 3)
      regs stk (readRegs regs value present none) (transferStacks src dst stk) := by
  have h := halt_after_trace _ (transferProgram_trace src dst value present hsd hvp regs stk)
    3 rfl rfl
  simpa [Run, transferProgram, transferResult, Nat.add_assoc] using h

theorem copy_run {r s : ℕ} (src dst tmp : Fin s) (value present : Fin r)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (hvp : value ≠ present)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (htmp : stk tmp = []) :
    Run (copyProgram src dst tmp value present) (7 * (stk src).length + 5)
      regs stk (readRegs regs value present none) (copyStacks src dst stk) := by
  have h := halt_after_trace _ (copyProgram_trace src dst tmp value present
    hsd hst htd hvp regs stk htmp) 7 rfl rfl
  simpa [Run, copyProgram, copyResult, Nat.add_assoc] using h

/-- Logical registers occupy the first `v` stacks. -/
def port {v : ℕ} (i : Fin v) : Fin (v + 3) := Fin.castAdd 3 i

/-- Scratch allocation is fixed, independently of all register contents. -/
def temp (v : ℕ) (i : Fin 3) : Fin (v + 3) := Fin.natAdd v i

@[simp] theorem port_inj {v : ℕ} {i j : Fin v} : port i = port j ↔ i = j :=
  Fin.castAdd_inj

@[simp] theorem temp_inj {v : ℕ} {i j : Fin 3} : temp v i = temp v j ↔ i = j := by
  simp [temp, Fin.ext_iff]

@[simp] theorem port_ne_temp {v : ℕ} (i : Fin v) (j : Fin 3) : port i ≠ temp v j := by
  intro h
  have hv := congrArg Fin.val h
  simp [port, temp] at hv
  omega

@[simp] theorem temp_ne_port {v : ℕ} (i : Fin 3) (j : Fin v) : temp v i ≠ port j :=
  (port_ne_temp j i).symm

def wordStore {v : ℕ} (words : Fin v → List Bool) : Stacks (Fin (v + 3)) :=
  Fin.addCases words (fun _ => [])

@[simp] theorem wordStore_port {v : ℕ} (words : Fin v → List Bool) (i : Fin v) :
    wordStore words (port i) = words i := by simp [wordStore, port]

@[simp] theorem wordStore_temp {v : ℕ} (words : Fin v → List Bool) (i : Fin 3) :
    wordStore words (temp v i) = [] := by simp [wordStore, temp]

theorem wordStore_update {v : ℕ} (words : Fin v → List Bool) (i : Fin v)
    (word : List Bool) :
    wordStore (Function.update words i word) =
      Function.update (wordStore words) (port i) word := by
  funext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · change wordStore (Function.update words i word) (port k) =
      Function.update (wordStore words) (port i) word (port k)
    simp only [wordStore_port, Function.update_apply, port_inj]
  · change wordStore (Function.update words i word) (temp v k) =
      Function.update (wordStore words) (port i) word (temp v k)
    simp

def reset (regs : Fin 2 → Bool) : Fin 2 → Bool := readRegs regs 0 1 none

@[simp] theorem reset_reset (regs : Fin 2 → Bool) : reset (reset regs) = reset regs :=
  readRegs_reset _ _ _ _

/-- Snapshot the source before modifying the destination, so all aliases work. -/
abbrev assignProgram {v : ℕ} (dst src : Fin v) : Program 2 (v + 3) 19 :=
  link (copyProgram (port src) (temp v 0) (temp v 1) 0 1)
    (link (clearProgram (port dst) 0 1)
      (link (transferProgram (temp v 0) (temp v 1) 0 1)
        (transferProgram (temp v 1) (port dst) 0 1)))

abbrev prependProgram {v : ℕ} (dst src : Fin v) : Program 2 (v + 3) 16 :=
  link (copyProgram (port src) (temp v 0) (temp v 1) 0 1)
    (link (transferProgram (temp v 0) (temp v 1) 0 1)
      (transferProgram (temp v 1) (port dst) 0 1))

abbrev appendProgram {v : ℕ} (dst src : Fin v) : Program 2 (v + 3) 24 :=
  link (copyProgram (port src) (temp v 0) (temp v 1) 0 1)
    (link (transferProgram (port dst) (temp v 2) 0 1)
      (link (transferProgram (temp v 0) (temp v 1) 0 1)
        (link (transferProgram (temp v 1) (port dst) 0 1)
          (transferProgram (temp v 2) (port dst) 0 1))))

theorem assign_stacks {v : ℕ} (dst src : Fin v) (words : Fin v → List Bool) :
    transferStacks (temp v 1) (port dst)
      (transferStacks (temp v 0) (temp v 1)
        (clearStacks (port dst) (copyStacks (port src) (temp v 0) (wordStore words)))) =
      wordStore (Function.update words dst (words src)) := by
  funext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · change (_ : Stacks (Fin (v + 3))) (port k) =
      wordStore (Function.update words dst (words src)) (port k)
    by_cases h : k = dst
    · subst k; simp [transferStacks, clearStacks, copyStacks]
    · simp [transferStacks, clearStacks, copyStacks, h]
  · change (_ : Stacks (Fin (v + 3))) (temp v k) =
      wordStore (Function.update words dst (words src)) (temp v k)
    fin_cases k <;> simp [transferStacks, clearStacks, copyStacks]

theorem prepend_stacks {v : ℕ} (dst src : Fin v) (words : Fin v → List Bool) :
    transferStacks (temp v 1) (port dst)
      (transferStacks (temp v 0) (temp v 1)
        (copyStacks (port src) (temp v 0) (wordStore words))) =
      wordStore (Function.update words dst (words src ++ words dst)) := by
  funext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · change (_ : Stacks (Fin (v + 3))) (port k) =
      wordStore (Function.update words dst (words src ++ words dst)) (port k)
    by_cases h : k = dst
    · subst k; simp [transferStacks, copyStacks]
    · simp [transferStacks, copyStacks, h]
  · change (_ : Stacks (Fin (v + 3))) (temp v k) =
      wordStore (Function.update words dst (words src ++ words dst)) (temp v k)
    fin_cases k <;> simp [transferStacks, copyStacks]

theorem append_stacks {v : ℕ} (dst src : Fin v) (words : Fin v → List Bool) :
    transferStacks (temp v 2) (port dst)
      (transferStacks (temp v 1) (port dst)
        (transferStacks (temp v 0) (temp v 1)
          (transferStacks (port dst) (temp v 2)
            (copyStacks (port src) (temp v 0) (wordStore words))))) =
      wordStore (Function.update words dst (words dst ++ words src)) := by
  funext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · change (_ : Stacks (Fin (v + 3))) (port k) =
      wordStore (Function.update words dst (words dst ++ words src)) (port k)
    by_cases h : k = dst
    · subst k; simp [transferStacks, copyStacks]
    · simp [transferStacks, copyStacks, h]
  · change (_ : Stacks (Fin (v + 3))) (temp v k) =
      wordStore (Function.update words dst (words dst ++ words src)) (temp v k)
    fin_cases k <;> simp [transferStacks, copyStacks]

theorem assign_run {v : ℕ} (dst src : Fin v) (regs : Fin 2 → Bool)
    (words : Fin v → List Bool) :
    Run (assignProgram dst src) (13 * (words src).length + 2 * (words dst).length + 14)
      regs (wordStore words) (reset regs) (wordStore (Function.update words dst (words src))) := by
  let s₁ := copyStacks (port src) (temp v 0) (wordStore words)
  let s₂ := clearStacks (port dst) s₁
  let s₃ := transferStacks (temp v 0) (temp v 1) s₂
  have t₁ := copy_run (port src) (temp v 0) (temp v 1) 0 1
    (by simp) (by simp) (by simp) (by decide) regs (wordStore words) (by simp)
  have t₂ := clear_run (port dst) 0 1 (reset regs) s₁
  have t₃ := transfer_run (temp v 0) (temp v 1) 0 1
    (by simp) (by decide) (reset regs) s₂
  have t₄ := transfer_run (temp v 1) (port dst) 0 1
    (by simp) (by decide) (reset regs) s₃
  simp only [reset, readRegs_reset] at t₂ t₃ t₄
  have total := link_run _ _ t₁ (link_run _ _ t₂ (link_run _ _ t₃ t₄))
  have h₁ : (s₁ (port dst)).length = (words dst).length := by simp [s₁, copyStacks]
  have h₂ : (s₂ (temp v 0)).length = (words src).length := by
    simp [s₂, s₁, clearStacks, copyStacks]
  have h₃ : (s₃ (temp v 1)).length = (words src).length := by
    simp [s₃, s₂, s₁, transferStacks, clearStacks, copyStacks]
  have hfinal : transferStacks (temp v 1) (port dst) s₃ =
      wordStore (Function.update words dst (words src)) := assign_stacks dst src words
  rw [hfinal] at total
  simp only [wordStore_port, h₁, h₂, h₃] at total
  convert total using 1
  · ring
  · simp [reset, readRegs]

theorem prepend_run {v : ℕ} (dst src : Fin v) (regs : Fin 2 → Bool)
    (words : Fin v → List Bool) :
    Run (prependProgram dst src) (13 * (words src).length + 11)
      regs (wordStore words) (reset regs)
      (wordStore (Function.update words dst (words src ++ words dst))) := by
  let s₁ := copyStacks (port src) (temp v 0) (wordStore words)
  let s₂ := transferStacks (temp v 0) (temp v 1) s₁
  have t₁ := copy_run (port src) (temp v 0) (temp v 1) 0 1
    (by simp) (by simp) (by simp) (by decide) regs (wordStore words) (by simp)
  have t₂ := transfer_run (temp v 0) (temp v 1) 0 1
    (by simp) (by decide) (reset regs) s₁
  have t₃ := transfer_run (temp v 1) (port dst) 0 1
    (by simp) (by decide) (reset regs) s₂
  simp only [reset, readRegs_reset] at t₂ t₃
  have total := link_run _ _ t₁ (link_run _ _ t₂ t₃)
  have h₁ : (s₁ (temp v 0)).length = (words src).length := by simp [s₁, copyStacks]
  have h₂ : (s₂ (temp v 1)).length = (words src).length := by
    simp [s₂, s₁, transferStacks, copyStacks]
  have hfinal : transferStacks (temp v 1) (port dst) s₂ =
      wordStore (Function.update words dst (words src ++ words dst)) :=
    prepend_stacks dst src words
  rw [hfinal] at total
  simp only [wordStore_port, h₁, h₂] at total
  convert total using 1
  · ring
  · simp [reset, readRegs]

theorem append_run {v : ℕ} (dst src : Fin v) (regs : Fin 2 → Bool)
    (words : Fin v → List Bool) :
    Run (appendProgram dst src) (13 * (words src).length + 6 * (words dst).length + 17)
      regs (wordStore words) (reset regs)
      (wordStore (Function.update words dst (words dst ++ words src))) := by
  let s₁ := copyStacks (port src) (temp v 0) (wordStore words)
  let s₂ := transferStacks (port dst) (temp v 2) s₁
  let s₃ := transferStacks (temp v 0) (temp v 1) s₂
  let s₄ := transferStacks (temp v 1) (port dst) s₃
  have t₁ := copy_run (port src) (temp v 0) (temp v 1) 0 1
    (by simp) (by simp) (by simp) (by decide) regs (wordStore words) (by simp)
  have t₂ := transfer_run (port dst) (temp v 2) 0 1
    (by simp) (by decide) (reset regs) s₁
  have t₃ := transfer_run (temp v 0) (temp v 1) 0 1
    (by simp) (by decide) (reset regs) s₂
  have t₄ := transfer_run (temp v 1) (port dst) 0 1
    (by simp) (by decide) (reset regs) s₃
  have t₅ := transfer_run (temp v 2) (port dst) 0 1
    (by simp) (by decide) (reset regs) s₄
  simp only [reset, readRegs_reset] at t₂ t₃ t₄ t₅
  have total := link_run _ _ t₁ (link_run _ _ t₂ (link_run _ _ t₃ (link_run _ _ t₄ t₅)))
  have h₁ : (s₁ (port dst)).length = (words dst).length := by simp [s₁, copyStacks]
  have h₂ : (s₂ (temp v 0)).length = (words src).length := by
    simp [s₂, s₁, transferStacks, copyStacks]
  have h₃ : (s₃ (temp v 1)).length = (words src).length := by
    simp [s₃, s₂, s₁, transferStacks, copyStacks]
  have h₄ : (s₄ (temp v 2)).length = (words dst).length := by
    simp [s₄, s₃, s₂, s₁, transferStacks, copyStacks]
  have hfinal : transferStacks (temp v 2) (port dst) s₄ =
      wordStore (Function.update words dst (words dst ++ words src)) :=
    append_stacks dst src words
  rw [hfinal] at total
  simp only [wordStore_port, h₁, h₂, h₃, h₄] at total
  convert total using 1
  · ring
  · simp [reset, readRegs]

abbrev headProgram {v : ℕ} (src : Fin v) : Program 2 (v + 3) 2 where
  inputStack := port src
  outputStack := port src
  entry := 0
  code := ![.peek (port src) 0 1 1, .halt]

abbrev tailProgram {v : ℕ} (src : Fin v) : Program 2 (v + 3) 2 where
  inputStack := port src
  outputStack := port src
  entry := 0
  code := ![.pop (port src) 0 1 1, .halt]

theorem head_run {v : ℕ} (src : Fin v) (regs : Fin 2 → Bool)
    (words : Fin v → List Bool) :
    Run (headProgram src) 2 regs (wordStore words)
      (readRegs regs 0 1 (words src).head?) (wordStore words) := by
  refine .cons (b := ⟨some 1, readRegs regs 0 1 (words src).head?, wordStore words⟩) ?_
    (.cons ?_ (.refl _))
  · simp [step, execInstr]
  · simp [step, execInstr]

theorem tail_run {v : ℕ} (src : Fin v) (regs : Fin 2 → Bool)
    (words : Fin v → List Bool) :
    Run (tailProgram src) 2 regs (wordStore words)
      (readRegs regs 0 1 (words src).head?)
      (wordStore (Function.update words src (words src).tail)) := by
  refine .cons (b := ⟨some 1, readRegs regs 0 1 (words src).head?,
    wordStore (Function.update words src (words src).tail)⟩) ?_ (.cons ?_ (.refl _))
  · simp [step, execInstr, wordStore_update]
  · simp [step, execInstr]

theorem clear_word_run {v : ℕ} (dst : Fin v) (regs : Fin 2 → Bool)
    (words : Fin v → List Bool) :
    Run (clearProgram (port dst) 0 1) (2 * (words dst).length + 3)
      regs (wordStore words) (reset regs) (wordStore (Function.update words dst [])) := by
  simpa only [wordStore_port, wordStore_update, clearStacks, reset] using
    clear_run (port dst) 0 1 regs (wordStore words)

/-- Only two Boolean flags are bounded data; all words remain unbounded lists. -/
structure State (v : ℕ) where
  bits : Fin 2 → Bool
  words : Fin v → List Bool

def State.toStructured {v : ℕ} (a : State v) : StructuredCalls.State 2 (v + 3) :=
  ⟨a.bits, wordStore a.words⟩

inductive Op (v : ℕ) where
  | clear (dst : Fin v)
  | assign (dst src : Fin v)
  | prepend (dst src : Fin v)
  | append (dst src : Fin v)
  | head (src : Fin v)
  | tail (src : Fin v)

namespace Op

def eval {v : ℕ} (op : Op v) (a : State v) : State v :=
  match op with
  | .clear dst => ⟨reset a.bits, Function.update a.words dst []⟩
  | .assign dst src => ⟨reset a.bits, Function.update a.words dst (a.words src)⟩
  | .prepend dst src => ⟨reset a.bits, Function.update a.words dst (a.words src ++ a.words dst)⟩
  | .append dst src => ⟨reset a.bits, Function.update a.words dst (a.words dst ++ a.words src)⟩
  | .head src => ⟨readRegs a.bits 0 1 (a.words src).head?, a.words⟩
  | .tail src => ⟨readRegs a.bits 0 1 (a.words src).head?,
      Function.update a.words src (a.words src).tail⟩

/-- This exact cost is justified by `run` below, not supplied as an annotation. -/
def time {v : ℕ} (op : Op v) (a : State v) : ℕ :=
  match op with
  | .clear dst => 2 * (a.words dst).length + 3
  | .assign dst src => 13 * (a.words src).length + 2 * (a.words dst).length + 14
  | .prepend _ src => 13 * (a.words src).length + 11
  | .append dst src => 13 * (a.words src).length + 6 * (a.words dst).length + 17
  | .head _ | .tail _ => 2

abbrev labels {v : ℕ} : Op v → ℕ
  | .clear _ => 3
  | .assign _ _ => 19
  | .prepend _ _ => 16
  | .append _ _ => 24
  | .head _ | .tail _ => 2

/-- The executable table depends on the operation and its fixed port indices,
not on the contents or lengths of any word. -/
abbrev program {v : ℕ} (op : Op v) : Program 2 (v + 3) op.labels :=
  match op with
  | .clear dst => clearProgram (port dst) 0 1
  | .assign dst src => assignProgram dst src
  | .prepend dst src => prependProgram dst src
  | .append dst src => appendProgram dst src
  | .head src => headProgram src
  | .tail src => tailProgram src

theorem run {v : ℕ} (op : Op v) (a : State v) :
    Run op.program (op.time a) a.bits (wordStore a.words)
      (op.eval a).bits (wordStore (op.eval a).words) := by
  cases op with
  | clear dst => exact clear_word_run dst a.bits a.words
  | assign dst src => exact assign_run dst src a.bits a.words
  | prepend dst src => exact prepend_run dst src a.bits a.words
  | append dst src => exact append_run dst src a.bits a.words
  | head src => exact head_run src a.bits a.words
  | tail src => exact tail_run src a.bits a.words

theorem primitive_run {v : ℕ} (op : Op v) (a : State v) :
    Computation.RunsIn (BitProgram.primitive op.program).step
      (primitiveOverhead op.program * op.time a)
      (primitiveCfg op.program ⟨some op.program.entry, a.bits, wordStore a.words⟩)
      (primitiveCfg op.program ⟨none, (op.eval a).bits, wordStore (op.eval a).words⟩) :=
  primitive_trace op.program (op.run a)

theorem labels_le {v : ℕ} (op : Op v) : op.labels ≤ 24 := by
  cases op <;> simp [labels]

/-- Direct use inside the verified structured compiler's loops and branches. -/
theorem call_eval {v : ℕ} (op : Op v) (a : State v) :
    StructuredCalls.Eval (.call op.program) (op.time a)
      a.toStructured (op.eval a).toStructured :=
  .call op.program (op.run a)

/-- A uniform linear bound on each implemented word operation. -/
theorem time_le {v : ℕ} (op : Op v) (a : State v) (bound : ℕ)
    (hbound : ∀ i, (a.words i).length ≤ bound) : op.time a ≤ 19 * bound + 17 := by
  cases op with
  | clear dst => simp only [time]; have := hbound dst; omega
  | assign dst src => simp only [time]; have := hbound dst; have := hbound src; omega
  | prepend dst src => simp only [time]; have := hbound src; omega
  | append dst src => simp only [time]; have := hbound dst; have := hbound src; omega
  | head src => simp only [time]; omega
  | tail src => simp only [time]; omega

end Op

/-- The empty script still has one real halt instruction. -/
abbrev emptyProgram (v : ℕ) : Program 2 (v + 3) 1 where
  inputStack := temp v 0
  outputStack := temp v 0
  entry := 0
  code := fun _ => .halt

abbrev scriptLabels {v : ℕ} : List (Op v) → ℕ
  | [] => 1
  | op :: rest => op.labels + scriptLabels rest

/-- A fixed script is compiled once by joining its actual finite tables. -/
abbrev scriptProgram {v : ℕ} (script : List (Op v)) : Program 2 (v + 3) (scriptLabels script) :=
  match script with
  | [] => emptyProgram v
  | op :: rest => link op.program (scriptProgram rest)

def scriptEval {v : ℕ} : List (Op v) → State v → State v
  | [], a => a
  | op :: rest, a => scriptEval rest (op.eval a)

def scriptTime {v : ℕ} : List (Op v) → State v → ℕ
  | [], _ => 1
  | op :: rest, a => op.time a + scriptTime rest (op.eval a)

/-- All word-operation costs are connected to the single generated program.
Intermediate word values affect execution length, never program construction. -/
theorem script_run {v : ℕ} (script : List (Op v)) (a : State v) :
    Run (scriptProgram script) (scriptTime script a) a.bits (wordStore a.words)
      (scriptEval script a).bits (wordStore (scriptEval script a).words) := by
  induction script generalizing a with
  | nil => exact .cons rfl (.refl _)
  | cons op rest ih => exact link_run _ _ (op.run a) (ih (op.eval a))

theorem script_primitive_run {v : ℕ} (script : List (Op v)) (a : State v) :
    Computation.RunsIn (BitProgram.primitive (scriptProgram script)).step
      (primitiveOverhead (scriptProgram script) * scriptTime script a)
      (primitiveCfg (scriptProgram script)
        ⟨some (scriptProgram script).entry, a.bits, wordStore a.words⟩)
      (primitiveCfg (scriptProgram script)
        ⟨none, (scriptEval script a).bits, wordStore (scriptEval script a).words⟩) :=
  primitive_trace (scriptProgram script) (script_run script a)

theorem script_call_eval {v : ℕ} (script : List (Op v)) (a : State v) :
    StructuredCalls.Eval (.call (scriptProgram script)) (scriptTime script a)
      a.toStructured (scriptEval script a).toStructured :=
  .call (scriptProgram script) (script_run script a)

/-- This static size bound has no dependence on word lengths. -/
theorem scriptLabels_le {v : ℕ} (script : List (Op v)) :
    scriptLabels script ≤ 24 * script.length + 1 := by
  induction script with
  | nil => simp [scriptLabels]
  | cons op rest ih =>
      have := op.labels_le
      simp only [scriptLabels, List.length_cons]
      omega

end SubexponentialSAT.ListRegisterProgram

end OAI.Algorithms
