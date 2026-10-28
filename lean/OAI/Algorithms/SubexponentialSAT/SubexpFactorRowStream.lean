import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorLabelProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.FactorPacketRows
import OAI.Algorithms.SubexponentialSAT.SubexpArgumentProgram

namespace OAI.Algorithms

/-!
# Actual value/label rows from a Boolean table

The input is the reversed payload returned by the outer record parser.
Consequently it is in ascending numeric-rank order. The fixed loop increments
an actual binary counter and prepends each framed row, recovering the original
descending table order without a supplied label stream.
-/

namespace SubexponentialSAT.SubexpFactorRowStream

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Word := List Bool
abbrev Data := State 8 26
abbrev RawRow := Subexp.FactorPacketRows.RawRow

structure View where
  modulus : Word
  rank : Word
  arity : Word
  input : Word
  zero : Word
  one : Word
  labels : Word := []
  value : Word := []
  payload : Word := []
  output : Word := []

def store (v : View) : Fin 26 → Word := fun i =>
  if i = 5 then v.modulus else if i = 13 then v.rank else if i = 14 then v.arity
  else if i = 16 then v.labels else if i = 17 then v.input else if i = 18 then v.zero
  else if i = 19 then v.one else if i = 20 then v.value else if i = 21 then v.payload
  else if i = 22 then v.output else []

def state (regs : Fin 8 → Bool) (v : View) : Data := ⟨regs, store v⟩

def scalar (v : View) (answer : Bool) : Word := if answer then v.one else v.zero

def row (modulus : Word) (k : ℕ) (zero one rank : Word) (answer : Bool) : RawRow :=
  ⟨if answer then one else zero, SubexpBasePUnranking.digitWords modulus k rank⟩

def forwardRows (modulus : Word) (k : ℕ) (zero one : Word) : Word → Word → List RawRow
  | _, [] => []
  | rank, answer :: answers => row modulus k zero one rank answer ::
      forwardRows modulus k zero one (CounterPrograms.ripple true rank) answers

def finalRank : Word → Word → Word
  | rank, [] => rank
  | rank, _ :: answers => finalRank (CounterPrograms.ripple true rank) answers

def tableRows (modulus : Word) (k : ℕ) (zero one answers : Word) : List RawRow :=
  (forwardRows modulus k zero one [] answers.reverse).reverse

def labelPorts : Fin 17 ↪ Fin 26 := ⟨Fin.castAdd 9, Fin.castAdd_injective _ _⟩
def writerRegs : Fin 5 ↪ Fin 8 := ⟨Fin.castAdd 3, Fin.castAdd_injective _ _⟩
def writerPorts (target : Fin 26) : Fin 6 → Fin 26 := ![0, 21, 1, target, 23, 24]
def counterRegs : Fin 3 ↪ Fin 8 := ⟨Fin.castAdd 5, Fin.castAdd_injective _ _⟩
def counterPorts : Fin 2 ↪ Fin 26 := ⟨![13, 24], by decide⟩

abbrev labels : Cmd 8 26 := .call
  (ProgramLinking.liftProgram SubexpFactorLabelProgram.program id labelPorts)
abbrev choose : Cmd 8 26 := .ite 0
  (.call (StackRoutines.copyProgram 19 20 23 0 1))
  (.call (StackRoutines.copyProgram 18 20 23 0 1))
abbrev transferValue : Cmd 8 26 := .call (StackRoutines.transferProgram 20 21 0 1)
abbrev write (target : Fin 26) : Cmd 8 26 := .call
  (ProgramLinking.liftProgram (SubexpArgumentProgram.writer true) writerRegs (writerPorts target))
abbrev removeTag : Cmd 8 26 := .base (.atom (.pop 16 0 1))
abbrev transferRow : Cmd 8 26 := .call (StackRoutines.transferProgram 16 21 0 1)
abbrev increment : Cmd 8 26 := .call
  (ProgramLinking.liftProgram (CounterPrograms.rippleProgram true) counterRegs counterPorts)
abbrev readAnswer : Cmd 8 26 := .base (.atom (.pop 17 0 1))

abbrev body : Cmd 8 26 := .seq choose (.seq labels (.seq transferValue
  (.seq (write 16) (.seq removeTag (.seq transferRow (.seq (write 22) increment))))))
abbrev loop : Cmd 8 26 := .while 1 (.seq body readAnswer)
abbrev seed : Cmd 8 26 := .seq (.base (.atom (.set 0 false))) (.base (.atom (.push 22 0)))
abbrev command : Cmd 8 26 := .seq seed (.seq readAnswer
  (.seq loop (.call (StackRoutines.clearProgram 13 0 1))))
def program := compiled command (17 : Fin 26) 22

@[simp] theorem forwardRows_length (modulus : Word) (k : ℕ) (zero one rank answers : Word) :
    (forwardRows modulus k zero one rank answers).length = answers.length := by
  induction answers generalizing rank with
  | nil => rfl
  | cons answer answers ih => simp only [forwardRows, List.length_cons, ih]

theorem finalRank_value (rank answers : Word) :
    CounterPrograms.value (finalRank rank answers) = CounterPrograms.value rank + answers.length := by
  induction answers generalizing rank with
  | nil => simp [finalRank]
  | cons answer answers ih =>
      simp only [finalRank, ih, CounterPrograms.value_increment, List.length_cons]
      omega

@[simp] theorem tableRows_length (modulus : Word) (k : ℕ) (zero one answers : Word) :
    (tableRows modulus k zero one answers).length = answers.length := by
  simp [tableRows]

theorem labels_length (modulus : Word) (k : ℕ) (zero one rank : Word) (answer : Bool) :
    (row modulus k zero one rank answer).labels.length = k := by
  simp [row]

private theorem embed_labels (regs oldRegs : Fin 8 → Bool) (v : View) (output : Word) :
    embedState id labelPorts (state oldRegs v)
      (SubexpFactorLabelProgram.state regs v.modulus v.rank v.arity [] [] output) =
      state regs {v with labels := output} := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id labelPorts.injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    have h16 : i ≠ 16 := fun h => hi ⟨16, h.symm⟩
    simp [state, store, h16]

theorem labels_eval (regs : Fin 8 → Bool) (v : View) (k : ℕ)
    (ha : v.arity = List.replicate k true) (hl : v.labels = []) :
    ∃ n ≤ SubexpFactorLabelProgram.budget v.modulus v.rank k, ∃ rf,
      Eval labels n (state regs v)
        (state rf {v with labels := (Encoding.encodeList id
          (SubexpBasePUnranking.digitWords v.modulus k v.rank))}) := by
  obtain ⟨rf, n, hn, ht⟩ := SubexpFactorLabelProgram.program_runsIn regs v.modulus v.rank k
  rw [← ha] at ht
  have he := eval_call_lifted SubexpFactorLabelProgram.program id labelPorts
    (state regs v) Function.injective_id labelPorts.injective ht
  rw [embed_labels, embed_labels] at he
  have hstart : ({v with labels := []} : View) = v := by cases v; simp_all
  rw [hstart] at he
  exact ⟨n, hn, rf, he⟩

theorem choose_eval (regs : Fin 8 → Bool) (v : View) (hv : v.value = []) :
    Eval choose (7 * (scalar v (regs 0)).length + 6) (state regs v)
      (state (readRegs regs 0 1 none) {v with value := scalar v (regs 0)}) := by
  have hcopy (source : Fin 26) (hs : source ≠ 20) (ht : source ≠ 23)
      (word : Word) (hw : store v source = word) :
      Eval (.call (StackRoutines.copyProgram source 20 23 0 1)) (7 * word.length + 5)
        (state regs v) (state (readRegs regs 0 1 none) {v with value := word}) := by
    have he := SubexpScanPrimitives.copy_eval (state regs v) source 20 23 0 1
      hs ht (by decide) (by decide) rfl
    have hst : StackRoutines.copyStacks source 20 (store v) = store {v with value := word} := by
      funext i
      by_cases h20 : i = 20
      · subst i
        change store v source ++ v.value = word
        rw [hw, hv, List.append_nil]
      · simp [StackRoutines.copyStacks, h20, store]
    simpa only [afterCopy, state, hw, hst] using he
  cases hanswer : regs 0 with
  | false =>
      have he := hcopy 18 (by decide) (by decide) v.zero rfl
      simpa [choose, scalar, hanswer, Nat.add_assoc] using
        (Eval.ite_false (yes := .call (StackRoutines.copyProgram 19 20 23 0 1)) hanswer he)
  | true =>
      have he := hcopy 19 (by decide) (by decide) v.one rfl
      simpa [choose, scalar, hanswer, Nat.add_assoc] using
        (Eval.ite_true (no := .call (StackRoutines.copyProgram 18 20 23 0 1)) hanswer he)

def written (target : Fin 26) (d : Data) : Data :=
  ⟨Function.update (Function.update d.regs 0 true) 1 false,
    Function.update (Function.update d.stacks 21 []) target
      (true :: (Encoding.frame (d.stacks 21).reverse ++ d.stacks target))⟩

theorem writerPorts_injective (target : Fin 26) (ht : target = 16 ∨ target = 22) :
    Function.Injective (writerPorts target) := by
  rcases ht with rfl | rfl <;> decide

theorem write_eval (target : Fin 26) (ht : target = 16 ∨ target = 22) (d : Data) :
    Eval (write target) (5 * (d.stacks 21).length + 7) d (written target d) := by
  have hp := writerPorts_injective target ht
  let small : State 5 6 := ⟨d.regs ∘ writerRegs, d.stacks ∘ writerPorts target⟩
  have hw := SubexpArgumentProgram.writer_eval true small (d.stacks 21).reverse
    (by simp [small, writerPorts])
  have hin : embedState writerRegs (writerPorts target) d small = d := by
    apply SubexpScanPrimitives.embedState_eq _ _ writerRegs.injective hp
    · intro i; rfl
    · intro i; rfl
    · intros; rfl
    · intros; rfl
  have hout : embedState writerRegs (writerPorts target) d
      (SubexpArgumentProgram.afterWriter true small (d.stacks 21).reverse) = written target d := by
    apply SubexpScanPrimitives.embedState_eq _ _ writerRegs.injective hp
    · intro i
      fin_cases i <;> simp [written, small, writerRegs,
 SubexpArgumentProgram.finishedRegs]
    · intro i
      rcases ht with rfl | rfl <;> fin_cases i <;>
        simp [written, small, writerPorts,
          SubexpArgumentProgram.destination]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, by simpa [writerRegs] using h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, by simpa [writerRegs] using h.symm⟩
      simp [written, h0, h1]
    · intro i hi
      have h21 : i ≠ 21 := fun h => hi ⟨1, by simpa [writerPorts] using h.symm⟩
      have htarget : i ≠ target := fun h => hi ⟨3, by simpa [writerPorts] using h.symm⟩
      simp [written, h21, htarget]
  cases hw with
  | call _ hw =>
      have he := eval_call_lifted (SubexpArgumentProgram.writer true) writerRegs
        (writerPorts target) d writerRegs.injective hp hw
      simpa only [write, hin, hout, List.length_reverse] using he

theorem transferValue_eval (regs : Fin 8 → Bool) (v : View) (hp : v.payload = []) :
    Eval transferValue (3 * v.value.length + 3) (state regs v)
      (state (readRegs regs 0 1 none) {v with value := [], payload := v.value.reverse}) := by
  have he := SubexpScanPrimitives.transfer_eval (state regs v) 20 21 0 1 (by decide) (by decide)
  have hs : afterTransfer (state regs v) 20 21 0 1 =
      state (readRegs regs 0 1 none) {v with value := [], payload := v.value.reverse} := by
    apply state_ext
    · rfl
    · funext i
      by_cases h20 : i = 20 <;> by_cases h21 : i = 21 <;>
        simp [afterTransfer, StackRoutines.transferStacks, state, store,
          h20, h21, hp]
  rw [hs] at he
  exact he

theorem transferRow_eval (regs : Fin 8 → Bool) (v : View) (hp : v.payload = []) :
    Eval transferRow (3 * v.labels.length + 3) (state regs v)
      (state (readRegs regs 0 1 none) {v with labels := [], payload := v.labels.reverse}) := by
  have he := SubexpScanPrimitives.transfer_eval (state regs v) 16 21 0 1 (by decide) (by decide)
  have hs : afterTransfer (state regs v) 16 21 0 1 =
      state (readRegs regs 0 1 none) {v with labels := [], payload := v.labels.reverse} := by
    apply state_ext
    · rfl
    · funext i
      by_cases h16 : i = 16 <;> by_cases h21 : i = 21 <;>
        simp [afterTransfer, StackRoutines.transferStacks, state, store,
          h16, h21, hp]
  rw [hs] at he
  exact he

theorem writeValue_eval (regs : Fin 8 → Bool) (v : View) (value : Word)
    (hp : v.payload = value.reverse) :
    Eval (write 16) (5 * value.length + 7) (state regs v)
      (state (Function.update (Function.update regs 0 true) 1 false)
        {v with payload := [], labels := true :: (Encoding.frame value ++ v.labels)}) := by
  have he := write_eval 16 (Or.inl rfl) (state regs v)
  have hs : written 16 (state regs v) =
      state (Function.update (Function.update regs 0 true) 1 false)
        {v with payload := [], labels := true :: (Encoding.frame value ++ v.labels)} := by
    apply state_ext
    · rfl
    · funext i
      by_cases h16 : i = 16 <;> by_cases h21 : i = 21 <;>
        simp [written, state, store, h16, h21, hp]
  rw [hs] at he
  change Eval (write 16) (5 * v.payload.length + 7) _ _ at he
  simpa only [hp, List.length_reverse] using he

theorem writeRow_eval (regs : Fin 8 → Bool) (v : View) (bits : Word)
    (hp : v.payload = bits.reverse) :
    Eval (write 22) (5 * bits.length + 7) (state regs v)
      (state (Function.update (Function.update regs 0 true) 1 false)
        {v with payload := [], output := true :: (Encoding.frame bits ++ v.output)}) := by
  have he := write_eval 22 (Or.inr rfl) (state regs v)
  have hs : written 22 (state regs v) =
      state (Function.update (Function.update regs 0 true) 1 false)
        {v with payload := [], output := true :: (Encoding.frame bits ++ v.output)} := by
    apply state_ext
    · rfl
    · funext i
      by_cases h22 : i = 22 <;> by_cases h21 : i = 21 <;>
        simp [written, state, store, h22, h21, hp]
  rw [hs] at he
  change Eval (write 22) (5 * v.payload.length + 7) _ _ at he
  simpa only [hp, List.length_reverse] using he

theorem removeTag_eval (regs : Fin 8 → Bool) (v : View) (bits : Word)
    (hl : v.labels = true :: bits) :
    Eval removeTag 1 (state regs v)
      (state (readRegs regs 0 1 (some true)) {v with labels := bits}) := by
  have he := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (16 : Fin 26) 0 1)
    (state regs v)
  apply Eval.base
  convert he using 1
  apply state_ext
  · simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, state, store, hl]
  · funext i
    by_cases h16 : i = 16 <;>
      simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr,
        state, store, hl, h16]

theorem increment_eval (regs : Fin 8 → Bool) (v : View) :
    Eval increment (CounterPrograms.rippleCost true v.rank + 1) (state regs v)
      (state (readRegs regs 0 1 none)
        {v with rank := CounterPrograms.ripple true v.rank}) := by
  let a : State 3 2 := ⟨CounterPrograms.counterRegs (regs 0) (regs 1) (regs 2),
    CounterPrograms.counterStacks v.rank []⟩
  let b : State 3 2 := ⟨CounterPrograms.counterRegs false false (regs 2),
    CounterPrograms.counterStacks (CounterPrograms.ripple true v.rank) []⟩
  have hbase : Trace (CounterPrograms.rippleProgram true)
      (CounterPrograms.rippleCost true v.rank)
      (a.withPC (some 0)) (b.withPC (some 10)) := by
    simpa [a, b, CounterPrograms.counterCfg] using
      CounterPrograms.ripple_trace true (regs 0) (regs 1) (regs 2) v.rank []
  have hhalt : Trace (CounterPrograms.rippleProgram true) 1
      (b.withPC (some 10)) (b.withPC none) := by
    refine .cons ?_ (.refl _)
    rfl
  have hrun := hbase.trans hhalt
  have he := eval_call_lifted (CounterPrograms.rippleProgram true) counterRegs counterPorts
    (state regs v) counterRegs.injective counterPorts.injective hrun
  have hin : embedState counterRegs counterPorts (state regs v) a = state regs v := by
    apply embedState_eq_of_ports _ _ _ _ _ counterRegs.injective counterPorts.injective
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hout : embedState counterRegs counterPorts (state regs v) b =
      state (readRegs regs 0 1 none) {v with rank := CounterPrograms.ripple true v.rank} := by
    apply embedState_eq_of_ports _ _ _ _ _ counterRegs.injective counterPorts.injective
    · intro i; fin_cases i <;> simp [state, readRegs, b, counterRegs]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      simp [state, readRegs, h0, h1]
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h13 : i ≠ 13 := fun h => hi ⟨0, h.symm⟩
      simp [state, store, h13]
  simpa only [increment, hin, hout] using he

theorem readAnswer_eval (regs : Fin 8 → Bool) (v : View) :
    Eval readAnswer 1 (state regs v)
      (state (readRegs regs 0 1 v.input.head?) {v with input := v.input.tail}) := by
  apply Eval.base
  have he := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (17 : Fin 26) 0 1)
    (state regs v)
  convert he using 1
  apply state_ext
  · cases hi : v.input <;>
      simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr,
        state, store, hi]
  · funext i
    by_cases h17 : i = 17 <;> cases hi : v.input <;>
      simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr,
        state, store, hi, h17]

theorem seed_eval (regs : Fin 8 → Bool) (v : View) (ho : v.output = []) :
    Eval seed 2 (state regs v)
      (state (Function.update regs 0 false) {v with output := [false]}) := by
  have hs := StructuredProgram.Eval.atom (StructuredProgram.Atom.set (0 : Fin 8) false)
    (state regs v)
  have hp := StructuredProgram.Eval.atom (StructuredProgram.Atom.push (22 : Fin 26) 0)
    (state (Function.update regs 0 false) v)
  have hs' : Eval (.base (.atom (.set 0 false))) 1 (state regs v)
      (state (Function.update regs 0 false) v) := by
    exact Eval.base hs
  have hp' : Eval (.base (.atom (.push 22 0))) 1
      (state (Function.update regs 0 false) v)
      (state (Function.update regs 0 false) {v with output := [false]}) := by
    apply Eval.base
    convert hp using 1
    apply state_ext
    · rfl
    · funext i
      by_cases h22 : i = 22 <;>
        simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr,
          state, store, ho, h22]
  exact hs'.seq hp'

theorem clearRank_eval (regs : Fin 8 → Bool) (v : View) :
    Eval (.call (StackRoutines.clearProgram 13 0 1)) (2 * v.rank.length + 3)
      (state regs v) (state (readRegs regs 0 1 none) {v with rank := []}) := by
  have he := ListRegisterProgram.clear_run (13 : Fin 26) (0 : Fin 8) 1
    regs (store v)
  have hs : Function.update (store v) 13 [] = store {v with rank := []} := by
    funext i
    by_cases h13 : i = 13 <;> simp [store, h13]
  have hsource : store v (13 : Fin 26) = v.rank := rfl
  apply Eval.call
  simpa only [state, StackRoutines.clearStacks, hs, hsource] using he

end SubexponentialSAT.SubexpFactorRowStream

end OAI.Algorithms
