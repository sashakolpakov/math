import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CollisionStreamProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-!
# Physical mismatch-position selection

The input consists of two packed arrays, a runtime row width, and a framed
list of numeric positions. Each callback reads the two rows with the actual
persistent array reader, compares their bytes, and emits exactly the unequal
positions. The arrays and their order are preserved.
-/

namespace SubexponentialSAT.Subexp.MismatchPlanProgram

open BitProgram StructuredCalls StackRoutines

abbrev Word := List Bool
abbrev Regs := Fin 8 → Bool
abbrev Data := State 8 16

abbrev state (regs : Regs) (left right width source payload acc output : Word) : Data :=
  ⟨regs, ![left, [], [], width, [], [], [], [], source, payload,
    right, [], [], acc, output, []]⟩

def arrayPort (right : Bool) : Fin 16 := if right then 10 else 0
def rowPort (right : Bool) : Fin 16 := if right then 12 else 1
def lookupPorts (right : Bool) : Fin 8 → Fin 16 :=
  ![arrayPort right, rowPort right, 2, 3, 4, 5, 6, 7]

theorem lookupPorts_injective (right : Bool) : Function.Injective (lookupPorts right) := by
  cases right <;> decide

abbrev lookup (right : Bool) : Cmd 8 16 :=
  .call (ProgramLinking.liftProgram (ArrayUpdatePrograms.readProgram (0 : Fin 8) 1)
    id (lookupPorts right))

abbrev afterLookup (right : Bool) (row : Word) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks 2 []) (rowPort right) row⟩

theorem lookup_eval (right : Bool) (rows : List Word) (width index : Word) (a : Data)
    (ha : a.stacks (arrayPort right) = rows.flatten)
    (hw : a.stacks 3 = width) (hi : a.stacks 2 = index)
    (hindex : index.length < rows.length)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hout : a.stacks (rowPort right) = [])
    (h4 : a.stacks 4 = []) (h5 : a.stacks 5 = [])
    (h6 : a.stacks 6 = []) (h7 : a.stacks 7 = []) :
    Eval (lookup right) (index.length * (14 * width.length + 10) + 15 * width.length + 16)
      a (afterLookup right (rows.getD index.length []) a) := by
  let inner : State 8 8 := ⟨a.regs, a.stacks ∘ lookupPorts right⟩
  have htake : (rows.take index.length).length = index.length := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hindex)]
  have hrow : (rows.getD index.length []).length = width.length := by
    rw [List.getD_eq_getElem _ _ hindex]
    exact hrows _ (List.getElem_mem hindex)
  have ht := ArrayUpdatePrograms.readProgram_trace (0 : Fin 8) 1 (by decide)
    (rows.take index.length) (rows.getD index.length [])
    (rows.drop (index.length + 1)).flatten width index inner.regs inner.stacks
    (by simpa [inner, lookupPorts] using ha.trans (GatherProgram.row_decomposition rows _ hindex))
    (by simpa [inner, lookupPorts] using hw) (by simpa [inner, lookupPorts] using hi)
    htake.symm (fun row hr => hrows row (List.mem_of_mem_take hr)) hrow
    (by simpa [inner, lookupPorts] using h4) (by simpa [inner, lookupPorts] using h5)
    (by simpa [inner, lookupPorts] using h6) (by simpa [inner, lookupPorts] using h7)
  have hin : embedState id (lookupPorts right) a inner = a := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id (lookupPorts_injective right)
    · intros; rfl
    · intros; rfl
    · intros; rfl
    · intros; rfl
  have hout' : embedState id (lookupPorts right) a
      ⟨readRegs inner.regs 0 1 none,
        ArrayUpdatePrograms.readStacks (rows.getD index.length []) inner.stacks⟩ =
      afterLookup right (rows.getD index.length []) a := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id (lookupPorts_injective right)
    · intros; rfl
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j; cases right <;> fin_cases j <;>
        simp_all [ inner, lookupPorts, rowPort, arrayPort, ArrayUpdatePrograms.readStacks]
    · intro j hj
      have h2 : j ≠ 2 := fun h => hj ⟨2, h.symm⟩
      have hr : j ≠ rowPort right := fun h => hj ⟨1, h.symm⟩
      simp [ h2, hr]
  have he := eval_call_lifted (ArrayUpdatePrograms.readProgram (0 : Fin 8) 1)
    id (lookupPorts right) a Function.injective_id (lookupPorts_injective right)
    (a := inner)
    (b := ⟨readRegs inner.regs 0 1 none,
      ArrayUpdatePrograms.readStacks (rows.getD index.length []) inner.stacks⟩) ht
  simpa only [hin, hout', htake, lookup] using he

abbrev copyIndex : Cmd 8 16 := .call (copyProgram 9 2 15 (0 : Fin 8) 1)
def afterCopy (a : Data) : Data := ⟨readRegs a.regs 0 1 none, copyStacks 9 2 a.stacks⟩

theorem copyIndex_eval (a : Data) (h15 : a.stacks 15 = []) :
    Eval copyIndex (7 * (a.stacks 9).length + 5) a (afterCopy a) :=
  TupleProgram.copy_eval 9 2 15 (0 : Fin 8) 1 (by decide) (by decide) (by decide)
    (by decide) a h15

def equalityRegs : Fin 5 → Fin 8 := Fin.castAdd 3
def equalityStacks : Fin 13 → Fin 16 := Fin.castAdd 3
theorem equalityRegs_injective : Function.Injective equalityRegs := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)
theorem equalityStacks_injective : Function.Injective equalityStacks := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 16 => x.val) h)

def equalityInner := compiled CollisionStreamProgram.sealCommand (1 : Fin 13) 11
abbrev equality : Cmd 8 16 :=
  .call (ProgramLinking.liftProgram equalityInner equalityRegs equalityStacks)

abbrev afterEquality (a : Data) (answer : Bool) : Data :=
  ⟨fun j => if j.val < 5 then false else a.regs j,
    Function.update (Function.update (Function.update a.stacks 1 []) 12 [])
      11 (answer :: a.stacks 11)⟩

theorem equality_eval (a : Data) :
    ∃ n ≤ 11 * (a.stacks 1).length + 2 * (a.stacks 12).length + 20,
      Eval equality n a (afterEquality a (decide (a.stacks 1 = a.stacks 12))) := by
  let inner : State 5 13 :=
    ⟨a.regs ∘ equalityRegs, a.stacks ∘ equalityStacks⟩
  obtain ⟨n, hn, ht⟩ := CollisionStreamProgram.seal_eval inner
  have hin : embedState equalityRegs equalityStacks a inner = a := by
    apply embedState_eq_of_ports _ _ _ _ _ equalityRegs_injective equalityStacks_injective
    · intros; rfl
    · intros; rfl
    · intros; rfl
    · intros; rfl
  have hout : embedState equalityRegs equalityStacks a
      (CollisionStreamProgram.sealed inner (decide (inner.stacks 1 = inner.stacks 12))) =
      afterEquality a (decide (a.stacks 1 = a.stacks 12)) := by
    apply embedState_eq_of_ports _ _ _ _ _ equalityRegs_injective equalityStacks_injective
    · intro j; fin_cases j <;> norm_num [afterEquality, CollisionStreamProgram.sealed, equalityRegs]
    · intro j hj
      have hge : ¬ j.val < 5 := by
        intro h; exact hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
      simp [ hge]
    · intro j
      fin_cases j <;>
        simp [ CollisionStreamProgram.sealed, inner, equalityStacks] ; rfl
    · intro j hj
      have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
      have h11 : j ≠ 11 := fun h => hj ⟨11, h.symm⟩
      have h12 : j ≠ 12 := fun h => hj ⟨12, h.symm⟩
      simp [ h1, h11, h12]
  have he := eval_call_lifted equalityInner equalityRegs equalityStacks a
    equalityRegs_injective equalityStacks_injective (compiled_halt_trace ht (1 : Fin 13) 11)
  refine ⟨n + 1, ?_, ?_⟩
  · have hn' : n ≤ 11 * (a.stacks 1).length + 2 * (a.stacks 12).length + 19 := by
      simpa [inner, equalityStacks] using hn
    omega
  · simpa only [hin, hout, equality] using he

def emitRegs : Fin 3 → Fin 8 := ![0, 1, 7]
def emitStacks : Fin 4 → Fin 16 := ![8, 3, 13, 9]
theorem emitRegs_injective : Function.Injective emitRegs := by decide
theorem emitStacks_injective : Function.Injective emitStacks := by decide

abbrev flags (regs : Regs) (v p f : Bool) : Regs :=
  Function.update (Function.update (Function.update regs 0 v) 1 p) 7 f

@[simp] theorem flags_self (regs : Regs) : flags regs (regs 0) (regs 1) (regs 7) = regs := by
  funext j; fin_cases j <;> simp [flags]

abbrev emit : Cmd 8 16 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.emitIfSelectedProgram emitRegs emitStacks)

private theorem embed_emit (regs : Regs) (v p f : Bool)
    (left right width source payload acc output source' width' acc' payload' : Word) :
    embedState emitRegs emitStacks (state regs left right width source payload acc output)
      (SubexpNormalizeProgram.filterState v p f source' width' acc' payload') =
      state (flags regs v p f) left right width' source' payload' acc' output := by
  apply embedState_eq_of_ports _ _ _ _ _ emitRegs_injective emitStacks_injective
  · intro j; fin_cases j <;> simp [ flags, emitRegs, SubexpNormalizeProgram.filterState,
      SubexpPostfixControl.triple]
  · intro j hj
    have h0 : j ≠ 0 := fun h => hj ⟨0, h.symm⟩
    have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
    have h7 : j ≠ 7 := fun h => hj ⟨2, h.symm⟩
    simp [ flags, h0, h1, h7]
  · intro j; fin_cases j <;> rfl
  · intro j hj
    have h8 : j ≠ 8 := fun h => hj ⟨0, h.symm⟩
    have h3 : j ≠ 3 := fun h => hj ⟨1, h.symm⟩
    have h13 : j ≠ 13 := fun h => hj ⟨2, h.symm⟩
    have h9 : j ≠ 9 := fun h => hj ⟨3, h.symm⟩
    fin_cases j <;> simp_all []

theorem emit_eval (bits left right width source acc output : Word) (regs : Regs) :
    Eval emit (SubexpNormalizeProgram.emitIfSelectedSteps (regs 7) bits + 1)
      (state regs left right width source bits.reverse acc output)
      (state (flags regs false true false) left right width source []
        (if regs 7 then true :: (Encoding.frame bits ++ acc) else acc) output) := by
  have ht := eval_call_lifted SubexpNormalizeProgram.emitIfSelectedProgram emitRegs emitStacks
    (state regs left right width source bits.reverse acc output) emitRegs_injective emitStacks_injective
    (SubexpNormalizeProgram.emitIfSelected_trace (regs 7) bits source width acc (regs 0) (regs 1))
  simpa only [embed_emit, flags_self, emit] using ht

abbrev markDifferent : Cmd 8 16 :=
  .seq (RecordPrograms.atom (.pop 11 7 1)) (RecordPrograms.atom (.bnot 7 7))

abbrev markedRegs (regs : Regs) (answer : Bool) : Regs :=
  Function.update (Function.update regs 1 true) 7 (!answer)

theorem markDifferent_eval (regs : Regs) (answer : Bool)
    (left right width source payload acc output : Word) :
    Eval markDifferent 2
      ⟨regs, Function.update (state regs left right width source payload acc output).stacks 11 [answer]⟩
      (state (markedRegs regs answer) left right width source payload acc output) := by
  let a : Data := ⟨regs, Function.update (state regs left right width source payload acc output).stacks 11 [answer]⟩
  let b := (StructuredProgram.Atom.pop (11 : Fin 16) (7 : Fin 8) 1).eval a
  have h1 : Eval (RecordPrograms.atom (.pop 11 7 1)) 1 a b := .base (.atom _ _)
  have h2 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.bnot (7 : Fin 8) 7) b)
  have ht := h1.seq h2
  convert ht using 1
  apply congrArg₂ StructuredProgram.State.mk
  · funext j; fin_cases j <;> simp [a, b, markedRegs, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
      execInstr, readRegs]
  · funext j; fin_cases j <;> simp [a, b, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
      execInstr]

local infixr:60 " ;; " => Cmd.seq

abbrev callback : Cmd 8 16 :=
  copyIndex ;; lookup false ;; copyIndex ;; lookup true ;; equality ;; markDifferent ;; emit

def keep (left right : List Word) (bits : Word) : Bool :=
  decide (left.getD bits.length [] ≠ right.getD bits.length [])

def callbackCost (width : ℕ) (bits : Word) : ℕ :=
  (28 * width + 39) * bits.length + 43 * width + 80

theorem callback_eval (left right : List Word) (width bits source acc output : Word) (regs : Regs)
    (hl : bits.length < left.length) (hr : bits.length < right.length)
    (hleft : ∀ row ∈ left, row.length = width.length)
    (hright : ∀ row ∈ right, row.length = width.length) :
    ∃ n ≤ callbackCost width.length bits, ∃ rf : Regs,
      rf 5 = regs 5 ∧ rf 6 = regs 6 ∧ rf 7 = false ∧
      Eval callback n (state regs left.flatten right.flatten width source bits.reverse acc output)
        (state rf left.flatten right.flatten width source []
          (if keep left right bits then true :: (Encoding.frame bits ++ acc) else acc) output) := by
  let a := state regs left.flatten right.flatten width source bits.reverse acc output
  let a1 := afterCopy a
  let a2 := afterLookup false (left.getD bits.length []) a1
  let a3 := afterCopy a2
  let a4 := afterLookup true (right.getD bits.length []) a3
  have h1 := copyIndex_eval a (by rfl)
  have h2 := lookup_eval false left width bits.reverse a1
    (by simp [a1, afterCopy, copyStacks, a, arrayPort])
    (by simp [a1, afterCopy, copyStacks, a ])
    (by simp [a1, afterCopy, copyStacks, a ])
    (by simpa using hl) hleft
    (by simp [a1, afterCopy, copyStacks, a, rowPort])
    (by simp [a1, afterCopy, copyStacks, a ])
    (by simp [a1, afterCopy, copyStacks, a ])
    (by simp [a1, afterCopy, copyStacks, a ])
    (by simp [a1, afterCopy, copyStacks, a ])
  have h3 := copyIndex_eval a2 (by simp [a2, a1, afterCopy, copyStacks, a, rowPort])
  have h4 := lookup_eval true right width bits.reverse a3
    (by simp [a3, afterCopy, copyStacks, a2, a1, a, arrayPort, rowPort])
    (by simp [a3, afterCopy, copyStacks, a2, a1, a, rowPort])
    (by simp [a3, afterCopy, copyStacks, a2, a1, a, rowPort])
    (by simpa using hr) hright
    (by simp [a3, afterCopy, copyStacks, a2, a1, a, rowPort])
    (by simp [a3, afterCopy, copyStacks, a2, a1, a, rowPort])
    (by simp [a3, afterCopy, copyStacks, a2, a1, a, rowPort])
    (by simp [a3, afterCopy, copyStacks, a2, a1, a, rowPort])
    (by simp [a3, afterCopy, copyStacks, a2, a1, a, rowPort])
  simp only [List.length_reverse] at h2 h4
  obtain ⟨ne, hne, he⟩ := equality_eval a4
  let answer := decide (left.getD bits.length [] = right.getD bits.length [])
  let re : Regs := fun j => if j.val < 5 then false else regs j
  have heout : afterEquality a4 (decide (a4.stacks 1 = a4.stacks 12)) =
      (⟨re, Function.update (state re left.flatten right.flatten width source bits.reverse acc output).stacks
        11 [answer]⟩ : Data) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j; fin_cases j <;> norm_num [afterEquality, a4, a3, a2, a1, a, afterCopy,
        afterLookup, readRegs, state, re]
    · funext j; fin_cases j <;> simp [ a4, a3, a2, a1, a, afterCopy, copyStacks, rowPort, answer]
  rw [heout] at he
  have hm := markDifferent_eval re answer left.flatten right.flatten width source bits.reverse acc output
  have hem := emit_eval bits left.flatten right.flatten width source acc output (markedRegs re answer)
  have hkeep : markedRegs re answer 7 = keep left right bits := by
    simp [markedRegs, answer, keep]
  rw [hkeep] at hem
  have ht := h1.seq (h2.seq (h3.seq (h4.seq (he.seq (hm.seq hem)))))
  have hllen : (left.getD bits.length []).length = width.length := by
    rw [List.getD_eq_getElem _ _ hl]; exact hleft _ (List.getElem_mem hl)
  have hrlen : (right.getD bits.length []).length = width.length := by
    rw [List.getD_eq_getElem _ _ hr]; exact hright _ (List.getElem_mem hr)
  let readCost := bits.length * (14 * width.length + 10) + 15 * width.length + 16
  let total := 7 * bits.length + 5 + (readCost +
    (7 * bits.length + 5 + (readCost +
      (ne + (2 + (SubexpNormalizeProgram.emitIfSelectedSteps (keep left right bits) bits + 1))))))
  refine ⟨total, ?_, flags (markedRegs re answer) false true false, ?_, ?_, ?_, ?_⟩
  · have hb := SubexpNormalizeProgram.emitIfSelected_steps_le (keep left right bits) bits
    have hleftRow : a4.stacks 1 = left.getD bits.length [] := by
      simp [a4, a3, a2, a1, a, afterCopy, copyStacks, rowPort]
    have hrightRow : a4.stacks 12 = right.getD bits.length [] := by
      simp [a4, a3, a2, a1, a, afterCopy, copyStacks, rowPort]
    rw [hleftRow, hrightRow, hllen, hrlen] at hne
    dsimp [callbackCost, total, readCost]
    nlinarith
  · change (if (5 : ℕ) < 5 then false else regs 5) = regs 5
    rfl
  · change (if (6 : ℕ) < 5 then false else regs 6) = regs 6
    rfl
  · simp [flags]
  · simpa [callback, total, readCost, a2, a1, a, afterLookup, afterCopy,
      copyStacks, rowPort, state] using ht

def ports : RecordPrograms.Ports 8 16 where
  tag := 5
  present := 6
  found := 7
  source := 8
  payload := 9
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

abbrev outerFlags (regs : Regs) (v p f : Bool) : Regs :=
  Function.update (Function.update (Function.update regs 5 v) 6 p) 7 f

@[simp] theorem outerFlags_self (regs : Regs) :
    outerFlags regs (regs 5) (regs 6) (regs 7) = regs := by
  funext j; fin_cases j <;> simp [outerFlags]

theorem recordState_state (regs : Regs) (v p f : Bool)
    (left right width source payload acc output source' payload' : Word) :
    RecordPrograms.state ports (state regs left right width source payload acc output)
      v p f source' payload' =
      state (outerFlags regs v p f) left right width source' payload' acc output := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext j; fin_cases j <;> simp [ ports ]

def invariant (left right : List Word) (width : Word) (a : Data) : Prop :=
  ∃ regs source payload acc,
    a = state regs left.flatten right.flatten width source payload acc []

theorem callback_contract (left right : List Word) (width : Word)
    (hleft : ∀ row ∈ left, row.length = width.length)
    (hright : ∀ row ∈ right, row.length = width.length) :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false)
      (callbackCost width.length) (invariant left right width)
      (SubexpNormalizeProgram.FilterEffect 13 (keep left right))
      (fun bits => bits.length < left.length ∧ bits.length < right.length) := by
  intro bits tail base hvalid hinv
  obtain ⟨regs, source, payload, acc, rfl⟩ := hinv
  obtain ⟨n, hn, rf, h5, h6, h7, he⟩ := callback_eval left right width bits tail acc []
    (outerFlags regs false true false) hvalid.1 hvalid.2 hleft hright
  let next := state rf left.flatten right.flatten width tail []
    (if keep left right bits then true :: (Encoding.frame bits ++ acc) else acc) []
  have hnext : RecordPrograms.state ports next false true false tail [] = next := by
    apply RecordPrograms.state_eq_self
    · simpa [next, state, ports, outerFlags] using h5
    · simpa [next, state, ports, outerFlags] using h6
    · exact h7
    · rfl
    · rfl
  refine ⟨n, next, hn, ⟨rf, tail, [], _, rfl⟩, ?_, ?_⟩
  · rfl
  · rw [hnext, recordState_state]
    exact he

theorem filter_eval (left right : List Word) (width : Word) (records : List Word) (regs : Regs)
    (hleft : ∀ row ∈ left, row.length = width.length)
    (hright : ∀ row ∈ right, row.length = width.length)
    (hvalid : ∀ bits ∈ records, bits.length < left.length ∧ bits.length < right.length) :
    ∃ n ≤ 3 + RecordPrograms.budget (callbackCost width.length) records, ∃ rf : Regs,
      Eval (RecordPrograms.iterate ports callback) n
        (state regs left.flatten right.flatten width (Encoding.encodeList id records) [] [false] [])
        (state rf left.flatten right.flatten width [] []
          (Encoding.encodeList id (records.filter (keep left right)).reverse) []) := by
  let base := state regs left.flatten right.flatten width
    (Encoding.encodeList id records) [] [false] []
  obtain ⟨n, next, hn, hnext, history, he⟩ := RecordPrograms.iterate_run_with_on
    ports callback (fun _ => false) (callbackCost width.length) (invariant left right width)
    (SubexpNormalizeProgram.FilterEffect 13 (keep left right))
    (fun bits => bits.length < left.length ∧ bits.length < right.length)
    (callback_contract left right width hleft hright) records [] base hvalid
    ⟨regs, _, [], [false], rfl⟩ (regs 5) (regs 6) (regs 7)
  have hout := SubexpNormalizeProgram.filterVisits_result 13 (keep left right) history [] rfl
  obtain ⟨rr, source, payload, acc, rfl⟩ := hnext
  have hacc : acc = Encoding.encodeList id (records.filter (keep left right)).reverse := by
    simpa [state] using hout
  rw [hacc] at he
  have hany : records.any (fun _ => false) = false := by induction records <;> simp_all
  have hunread : RecordPrograms.unread (fun _ => false) records [] = [] := by
    induction records <;> simp_all [RecordPrograms.unread]
  refine ⟨n, hn, outerFlags rr false true false, ?_⟩
  simpa only [base, List.append_nil, hany, hunread, recordState_state, outerFlags_self] using he

def reverseStacks : Fin 4 → Fin 16 := ![13, 3, 14, 9]
theorem reverseStacks_injective : Function.Injective reverseStacks := by decide

abbrev reverseCall : Cmd 8 16 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.reverseRecordsProgram emitRegs reverseStacks)

private theorem embed_reverse (regs : Regs) (v p f : Bool)
    (left right width source payload acc output acc' width' out' payload' : Word) :
    embedState emitRegs reverseStacks (state regs left right width source payload acc output)
      (SubexpNormalizeProgram.filterState v p f acc' width' out' payload') =
      state (flags regs v p f) left right width' source payload' acc' out' := by
  apply embedState_eq_of_ports _ _ _ _ _ emitRegs_injective reverseStacks_injective
  · intro j; fin_cases j <;> simp [ flags, emitRegs, SubexpNormalizeProgram.filterState,
      SubexpPostfixControl.triple]
  · intro j hj
    have h0 : j ≠ 0 := fun h => hj ⟨0, h.symm⟩
    have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
    have h7 : j ≠ 7 := fun h => hj ⟨2, h.symm⟩
    simp [ flags, h0, h1, h7]
  · intro j; fin_cases j <;> rfl
  · intro j hj
    have h13 : j ≠ 13 := fun h => hj ⟨0, h.symm⟩
    have h3 : j ≠ 3 := fun h => hj ⟨1, h.symm⟩
    have h14 : j ≠ 14 := fun h => hj ⟨2, h.symm⟩
    have h9 : j ≠ 9 := fun h => hj ⟨3, h.symm⟩
    fin_cases j <;> simp_all []

theorem reverse_eval (records : List Word) (left right width source : Word) (regs : Regs) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length,
      Eval reverseCall n
        (state regs left right width source [] (Encoding.encodeList id records) [false])
        (state (flags regs false true false) left right width source [] []
          (Encoding.encodeList id records.reverse)) := by
  obtain ⟨n, hn, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records [] [] width
    (regs 0) (regs 1) (regs 7)
  have he := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram emitRegs reverseStacks
    (state regs left right width source [] (Encoding.encodeList id records) [false])
    emitRegs_injective reverseStacks_injective ht
  refine ⟨n, hn, ?_⟩
  simpa only [List.append_nil, Encoding.encodeList, embed_reverse, flags_self, reverseCall] using he

abbrev initializeList (dst : Fin 16) : Cmd 8 16 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.push dst 0))

theorem initialize_eval (dst : Fin 16) (a : Data) :
    Eval (initializeList dst) 2 a
      ⟨Function.update a.regs 0 false, Function.update a.stacks dst (false :: a.stacks dst)⟩ := by
  have h1 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (0 : Fin 8) false) a)
  have h2 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push dst (0 : Fin 8))
    ((StructuredProgram.Atom.set (0 : Fin 8) false).eval a))
  exact h1.seq h2

abbrev command : Cmd 8 16 :=
  initializeList 13 ;; RecordPrograms.iterate ports callback ;; initializeList 14 ;; reverseCall

abbrev program : Program 8 16 (size command + 1) := compiled command 8 14

def sourceBound (width : ℕ) (records : List Word) : ℕ :=
  8 + RecordPrograms.budget (callbackCost width) records + 10 * (Encoding.encodeList id records).length

theorem encoded_filter_length_le (records : List Word) (test : Word → Bool) :
    (Encoding.encodeList id (records.filter test)).length ≤ (Encoding.encodeList id records).length := by
  induction records with
  | nil => simp
  | cons b bs ih =>
      cases h : test b <;> simp [ h, Encoding.length_encodeList_cons] <;> omega

theorem command_eval (left right : List Word) (width : Word) (records : List Word) (regs : Regs)
    (hleft : ∀ row ∈ left, row.length = width.length)
    (hright : ∀ row ∈ right, row.length = width.length)
    (hvalid : ∀ bits ∈ records, bits.length < left.length ∧ bits.length < right.length) :
    ∃ n, n + 1 ≤ sourceBound width.length records ∧ ∃ rf : Regs,
      Eval command n
        (state regs left.flatten right.flatten width (Encoding.encodeList id records) [] [] [])
        (state rf left.flatten right.flatten width [] [] []
          (Encoding.encodeList id (records.filter (keep left right)))) := by
  obtain ⟨n, hn, rf, he⟩ := filter_eval left right width records (Function.update regs 0 false)
    hleft hright hvalid
  obtain ⟨m, hm, hr⟩ := reverse_eval (records.filter (keep left right)).reverse
    left.flatten right.flatten width [] (Function.update rf 0 false)
  rw [List.reverse_reverse] at hr
  have hi := initialize_eval 13
    (state regs left.flatten right.flatten width (Encoding.encodeList id records) [] [] [])
  have ho := initialize_eval 14
    (state rf left.flatten right.flatten width [] []
      (Encoding.encodeList id (records.filter (keep left right)).reverse) [])
  have hi' : Eval (initializeList 13) 2
      (state regs left.flatten right.flatten width (Encoding.encodeList id records) [] [] [])
      (state (Function.update regs 0 false) left.flatten right.flatten width
        (Encoding.encodeList id records) [] [false] []) := by
    convert hi using 1
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j; fin_cases j <;> simp []
  have ho' : Eval (initializeList 14) 2
      (state rf left.flatten right.flatten width [] []
        (Encoding.encodeList id (records.filter (keep left right)).reverse) [])
      (state (Function.update rf 0 false) left.flatten right.flatten width [] []
        (Encoding.encodeList id (records.filter (keep left right)).reverse) [false]) := by
    convert ho using 1
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j; fin_cases j <;> simp []
  have hlen : (Encoding.encodeList id (records.filter (keep left right)).reverse).length ≤
      (Encoding.encodeList id records).length := by
    have hrev := ProgramEncoding.encodeRecords_length (records.filter (keep left right)).reverse
    have horig := ProgramEncoding.encodeRecords_length (records.filter (keep left right))
    have hf := encoded_filter_length_le records (keep left right)
    have hsame : (Encoding.encodeList id (records.filter (keep left right)).reverse).length =
        (Encoding.encodeList id (records.filter (keep left right))).length := by
      change (ProgramEncoding.encodeRecords _).length = (ProgramEncoding.encodeRecords _).length
      rw [hrev, horig]
      simp
    exact hsame.le.trans hf
  refine ⟨_, ?_, flags (Function.update rf 0 false) false true false, hi'.seq (he.seq (ho'.seq hr))⟩
  dsimp [sourceBound]
  omega

def indexRecords (positions : List ℕ) : List Word :=
  positions.map (fun i => List.replicate i true)

def mismatch (left right : List Word) (positions : List ℕ) : List ℕ :=
  positions.filter (fun i => decide (left.getD i [] ≠ right.getD i []))

theorem filter_indexRecords (left right : List Word) (positions : List ℕ) :
    (indexRecords positions).filter (keep left right) = indexRecords (mismatch left right positions) := by
  simp [indexRecords, mismatch, List.filter_map, keep, Function.comp_def]

theorem program_runsIn (left right : List Word) (width : Word) (positions : List ℕ) (regs : Regs)
    (hleft : ∀ row ∈ left, row.length = width.length)
    (hright : ∀ row ∈ right, row.length = width.length)
    (hvalid : ∀ i ∈ positions, i < left.length ∧ i < right.length) :
    ∃ rf : Regs, RunsIn program (sourceBound width.length (indexRecords positions))
      ((state regs left.flatten right.flatten width
        (ProgramEncoding.encodeRecords (indexRecords positions)) [] [] []).withPC (some program.entry))
      ((state rf left.flatten right.flatten width [] [] []
        (ProgramEncoding.encodeRecords (indexRecords (mismatch left right positions)))).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := command_eval left right width (indexRecords positions) regs hleft hright
    (by intro bits hb; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb; simpa using hvalid i hi)
  rw [filter_indexRecords] at he
  exact ⟨rf, n + 1, hn, compiled_halt_trace he 8 14⟩

theorem primitive_run (left right : List Word) (width : Word) (positions : List ℕ) (regs : Regs)
    (hleft : ∀ row ∈ left, row.length = width.length)
    (hright : ∀ row ∈ right, row.length = width.length)
    (hvalid : ∀ i ∈ positions, i < left.length ∧ i < right.length) :
    ∃ rf : Regs, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * sourceBound width.length (indexRecords positions))
      (primitiveCfg program ((state regs left.flatten right.flatten width
        (ProgramEncoding.encodeRecords (indexRecords positions)) [] [] []).withPC (some program.entry)))
      (primitiveCfg program ((state rf left.flatten right.flatten width [] [] []
        (ProgramEncoding.encodeRecords (indexRecords (mismatch left right positions)))).withPC none)) := by
  obtain ⟨rf, h⟩ := program_runsIn left right width positions regs hleft hright hvalid
  exact ⟨rf, primitive_execution program h⟩

end SubexponentialSAT.Subexp.MismatchPlanProgram

end OAI.Algorithms
