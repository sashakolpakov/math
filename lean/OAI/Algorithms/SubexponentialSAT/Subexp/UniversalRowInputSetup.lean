import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowWorkspace
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.SubexpFullShapeProgram

namespace OAI.Algorithms

/-! Actual setup of the bounded row evaluator's 49-stack workspace.

All parameters are read from persistent source stacks.  In particular, the
row count is obtained by popping the stored successor, the prime-field zero
is extracted from the stored zero quartet, and the row width is built by the
runtime block-copy program.  No matrix or correction vector is supplied.
-/

namespace SubexponentialSAT.Subexp.UniversalRowInputSetup

open BitProgram StructuredCalls StackRoutines
open UniversalRowWorkspace (port port_injective port_lt_cache)

abbrev Word := List Bool
abbrev Data := State 16 288
abbrev Code := Cmd 16 288

/-- The ten persistent masters copied before computing derived fields. -/
def seedSlots : List (Fin 49) := [21, 22, 23, 24, 25, 29, 31, 32, 46, 47]

def source (j : Fin 49) : Fin 288 :=
  if j = 21 then 252 else if j = 22 then 253
  else if j = 23 then 272 else if j = 24 then 275
  else if j = 25 then 284 else if j = 29 then 128
  else if j = 31 then 254 else if j = 32 then 243
  else if j = 46 then 133 else 131

theorem source_high (j : Fin 49) : 128 ≤ (source j).val := by
  unfold source
  split_ifs <;> decide

theorem high_ne_port (s : Fin 288) (hs : 128 ≤ s.val) (j : Fin 49) : s ≠ port j := by
  intro h
  have := port_lt_cache j
  rw [← h] at this
  omega

@[simp] theorem source_ne_port (i j : Fin 49) : source i ≠ port j :=
  high_ne_port _ (source_high i) j

def copyTo (src : Fin 288) (dst : Fin 49) : Code :=
  .call (copyProgram src (port dst) (port 44) (0 : Fin 16) 1)

def copied (a : Data) (src : Fin 288) (dst : Fin 49) : Data :=
  ⟨readRegs a.regs 0 1 none, copyStacks src (port dst) a.stacks⟩

theorem copied_native (a : Data) (src : Fin 288) (dst j : Fin 49) :
    (copied a src dst).stacks (port j) =
      if j = dst then a.stacks src ++ a.stacks (port dst) else a.stacks (port j) := by
  simp only [copied, copyStacks, Function.update_apply, port_injective.eq_iff]

theorem copied_source (a : Data) (i dst j : Fin 49) :
    (copied a (source i) dst).stacks (source j) = a.stacks (source j) := by
  simp +decide [copied, copyStacks]

theorem copyTo_eval (a : Data) (src : Fin 288) (dst : Fin 49)
    (hs : 128 ≤ src.val) (hd : dst ≠ 44) (ht : a.stacks (port 44) = []) :
    Eval (copyTo src dst) (7 * (a.stacks src).length + 5) a (copied a src dst) :=
  TupleProgram.copy_eval src (port dst) (port 44) (0 : Fin 16) 1
    (high_ne_port _ hs _) (high_ne_port _ hs _)
    (fun h => hd (port_injective h).symm) (by decide) a ht

def copySeeds : List (Fin 49) → Code
  | [] => .base .skip
  | j :: js => .seq (copyTo (source j) j) (copySeeds js)

def seedResult : List (Fin 49) → Data → Data
  | [], a => a
  | j :: js, a => seedResult js (copied a (source j) j)

def seedCost (js : List (Fin 49)) (a : Data) : ℕ :=
  (js.map fun j => 7 * (a.stacks (source j)).length + 5).sum

theorem seedResult_frame (js : List (Fin 49)) (a : Data) (k : Fin 288)
    (hk : ∀ j ∈ js, k ≠ port j) : (seedResult js a).stacks k = a.stacks k := by
  induction js generalizing a with
  | nil => rfl
  | cons j js ih =>
      rw [seedResult, ih _ (by intro i hi; exact hk i (by simp +decide [hi]))]
      simp +decide [copied, copyStacks, hk j (by simp)]

theorem copySeeds_eval (js : List (Fin 49)) (a : Data)
    (hj : ∀ j ∈ js, j ≠ 44) (ht : a.stacks (port 44) = []) :
    Eval (copySeeds js) (seedCost js a) a (seedResult js a) := by
  induction js generalizing a with
  | nil => exact .base (.skip _)
  | cons j js ih =>
      have hdst := hj j (by simp)
      have ht' : (copied a (source j) j).stacks (port 44) = [] := by
        simp +decide [copied, copyStacks, port_injective.ne hdst.symm, ht]
      have hc : seedCost js (copied a (source j) j) = seedCost js a := by
        unfold seedCost
        congr 1
        apply List.map_congr_left
        intro i hi
        simp +decide [copied, copyStacks]
      have he := (copyTo_eval a (source j) j (source_high j) hdst ht).seq
        (ih _ (by intro i hi; exact hj i (by simp +decide [hi])) ht')
      rw [hc] at he
      exact he

def seedNative (a : Data) (j : Fin 49) : Word :=
  if j ∈ seedSlots then a.stacks (source j) else []

theorem seed_native (a : Data) (hempty : ∀ j, a.stacks (port j) = []) (j : Fin 49) :
    (seedResult seedSlots a).stacks (port j) = seedNative a j := by
  fin_cases j <;>
    simp +decide [seedResult, seedSlots, copied_native, copied_source, seedNative, hempty]

def popRow : Code := .base (.atom (.pop (port 32) 0 1))

def popped (a : Data) (R : ℕ) : Data :=
  ⟨readRegs a.regs 0 1 (some true),
    Function.update a.stacks (port 32) (List.replicate R true)⟩

theorem popRow_eval (a : Data) (R : ℕ)
    (hR : a.stacks (port 32) = List.replicate (R + 1) true) :
    Eval popRow 1 a (popped a R) := by
  have h := Eval.base (StructuredProgram.Eval.atom
    (.pop (port 32) (0 : Fin 16) 1) a)
  simpa +decide [popRow, popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr,
    hR, List.replicate_succ] using h

def primeZero : Code :=
  .seq (copyTo 131 43)
    (.seq (SubexpScanPrimitives.takeWord 129 (port 42) (port 44) (port 43) (port 30)
      (0 : Fin 16) 1) (.call (clearProgram (port 43) (0 : Fin 16) 1)))

theorem primeZero_eval (a : Data) (b : ℕ)
    (hzero : a.stacks 131 = List.replicate (4 * b) false)
    (hwidth : (a.stacks 129).length = b)
    (h30 : a.stacks (port 30) = []) (h42 : a.stacks (port 42) = [])
    (h43 : a.stacks (port 43) = []) (h44 : a.stacks (port 44) = []) :
    Eval primeZero (48 * b + 19) a
      ⟨readRegs a.regs 0 1 none,
        Function.update a.stacks (port 30) (List.replicate b false)⟩ := by
  let a1 := copied a 131 43
  let a2 := SubexpScanPrimitives.afterTake a1 (port 43) (port 30) 0 1
    (List.replicate b false) (List.replicate (3 * b) false)
  have h1 := copyTo_eval a 131 43 (by decide) (by decide) h44
  have hsplit : a1.stacks (port 43) =
      List.replicate b false ++ List.replicate (3 * b) false := by
    simp only [a1, copied, copyStacks, Function.update_self, hzero, h43, List.append_nil]
    rw [← List.replicate_add]
    congr 1
    omega
  have h2 := SubexpScanPrimitives.takeWord_eval a1 129 (port 42) (port 44)
    (port 43) (port 30) (0 : Fin 16) 1 (by decide) (by decide)
    (List.replicate b false) (List.replicate (3 * b) false) hsplit
    (by simpa +decide [a1, copied, copyStacks, port] using h42)
    (by simpa +decide [a1, copied, copyStacks, port] using h44)
    (by simpa +decide [a1, copied, copyStacks, port] using hwidth)
  have h3 := TupleProgram.clear_eval (port 43) (0 : Fin 16) 1 a2
  have hend : (⟨readRegs a2.regs 0 1 none, clearStacks (port 43) a2.stacks⟩ : Data) =
      ⟨readRegs a.regs 0 1 none,
        Function.update a.stacks (port 30) (List.replicate b false)⟩ := by
    apply SubexpScanPrimitives.state_ext
    · simp +decide [a2, a1, copied, SubexpScanPrimitives.afterTake, readRegs_reset]
    · funext k
      by_cases hk43 : k = port 43
      · subst k
        simp +decide [clearStacks, h43]
      by_cases hk30 : k = port 30
      · subst k
        simp +decide [a2, a1, copied, SubexpScanPrimitives.afterTake, clearStacks,
          copyStacks, h30]
      · simp +decide [a2, a1, copied, SubexpScanPrimitives.afterTake, clearStacks,
          copyStacks, hk43, hk30]
  have hlen : (a2.stacks (port 43)).length = 3 * b := by
    simp +decide [a2, SubexpScanPrimitives.afterTake, port]
  have he := h1.seq (h2.seq h3)
  rw [hend] at he
  simpa only [primeZero, hzero, List.length_replicate, hlen,
    show 7 * (4 * b) + 5 + (14 * b + 11 + (2 * (3 * b) + 3)) = 48 * b + 19
      by omega] using he

def shapeRegs : Fin 3 → Fin 16 := Fin.castAdd 13
def shapePorts : Fin 4 → Fin 288 := ![port 21, port 26, port 15, port 42]
theorem shapeRegs_injective : Function.Injective shapeRegs := Fin.castAdd_injective 3 13
theorem shapePorts_injective : Function.Injective shapePorts := by decide

def reset : Code :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.set 1 false))) (.base (.atom (.set 2 false))))
def resetState (a : Data) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 0 false) 1 false) 2 false,
    a.stacks⟩
theorem reset_eval (a : Data) : Eval reset 3 a (resetState a) :=
  .seq (.base (.atom _ _)) (.seq (.base (.atom _ _)) (.base (.atom _ _)))

def rowWidth : Code :=
  .seq (copyTo 253 42) (.seq reset
    (.call (ProgramLinking.liftProgram SubexpFullShapeProgram.program shapeRegs shapePorts)))

theorem rowWidth_eval (a : Data) (Q r : ℕ)
    (hQ : a.stacks 253 = List.replicate Q true)
    (hr : a.stacks (port 21) = List.replicate r true)
    (h26 : a.stacks (port 26) = []) (h15 : a.stacks (port 15) = [])
    (h42 : a.stacks (port 42) = []) (h44 : a.stacks (port 44) = []) :
    Eval rowWidth (Q * (7 * r + 14) + 11) a
      ⟨(resetState a).regs,
        Function.update a.stacks (port 26) (List.replicate (Q * r) true)⟩ := by
  let copiedA := copied a 253 42
  let prepared := resetState copiedA
  let first := SubexpFullShapeProgram.inputState Q (List.replicate r true)
  let last := SubexpFullShapeProgram.outputState Q (List.replicate r true)
  let result : Data := ⟨(resetState a).regs,
    Function.update a.stacks (port 26) (List.replicate (Q * r) true)⟩
  have hin : embedState shapeRegs shapePorts prepared first = prepared := by
    apply embedState_eq_of_ports _ _ _ _ _ shapeRegs_injective shapePorts_injective
    · intro j
      fin_cases j <;> simp +decide [shapeRegs, prepared, resetState, first,
        SubexpFullShapeProgram.inputState, BlockCopyProgram.initialState, BlockCopyProgram.data]
    · intros; rfl
    · intro j
      fin_cases j <;> simp +decide [shapePorts, prepared, copiedA, copied, copyStacks, resetState,
        first, SubexpFullShapeProgram.inputState, BlockCopyProgram.initialState,
        BlockCopyProgram.data, hQ, hr, h26, h15, h42]
    · intros; rfl
  have hout : embedState shapeRegs shapePorts prepared last = result := by
    apply embedState_eq_of_ports _ _ _ _ _ shapeRegs_injective shapePorts_injective
    · intro j
      fin_cases j <;> simp +decide [shapeRegs, result, resetState, last,
        SubexpFullShapeProgram.outputState, BlockCopyProgram.data]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
      have h2 : j ≠ 2 := fun h => hj ⟨2, h.symm⟩
      simp +decide [result, prepared, resetState, copiedA, copied, readRegs, h0, h1, h2]
    · intro j
      fin_cases j <;> simp +decide [shapePorts, result, last, SubexpFullShapeProgram.outputState,
        SubexpFullShapeProgram.fullShape_unary, BlockCopyProgram.data, hr, h15, h42]
    · intro j hj
      have h26' : j ≠ port 26 := fun h => hj ⟨1, h.symm⟩
      have h42' : j ≠ port 42 := fun h => hj ⟨3, h.symm⟩
      simp +decide [result, prepared, resetState, copiedA, copied, copyStacks, h26', h42']
  have hshape := SubexpFullShapeProgram.lifted_eval shapeRegs shapePorts
    shapeRegs_injective shapePorts_injective prepared Q (List.replicate r true)
  rw [hin, hout] at hshape
  have hcopy := copyTo_eval a 253 42 (by decide) (by decide) h44
  have he := hcopy.seq ((reset_eval copiedA).seq hshape)
  have hcost : 7 * Q + 5 + (3 + (Q * (7 * r + 7) + 3)) =
      Q * (7 * r + 14) + 11 := by ring
  simpa only [rowWidth, result, hQ, List.length_replicate, hcost] using he

/-- Exact native input, including the two persistent constants used by the
correction-scalar routine.  All unlisted native stacks are empty. -/
def inputStacks (a : Data) (Q r R b : ℕ) : Fin 49 → Word :=
  Function.update (Function.update (Function.update (seedNative a)
    32 (List.replicate R true)) 30 (List.replicate b false))
    26 (List.replicate (Q * r) true)

theorem inputStacks_eq (a : Data) (Q r R b : ℕ)
    (hQ : a.stacks 253 = List.replicate Q true)
    (hr : a.stacks 252 = List.replicate r true) (j : Fin 49) :
    inputStacks a Q r R b j =
      if j = 21 then List.replicate r true
      else if j = 22 then List.replicate Q true
      else if j = 23 then a.stacks 272
      else if j = 24 then a.stacks 275
      else if j = 25 then a.stacks 284
      else if j = 26 then List.replicate (Q * r) true
      else if j = 29 then a.stacks 128
      else if j = 30 then List.replicate b false
      else if j = 31 then a.stacks 254
      else if j = 32 then List.replicate R true
      else if j = 46 then a.stacks 133
      else if j = 47 then a.stacks 131 else [] := by
  fin_cases j <;> simp +decide [inputStacks, seedNative, source, hQ, hr]

def command : Code :=
  .seq (copySeeds seedSlots) (.seq popRow (.seq primeZero rowWidth))

def budget (a : Data) (Q r b : ℕ) : ℕ :=
  seedCost seedSlots a + 1 + (48 * b + 19) + (Q * (7 * r + 14) + 11)

theorem budget_eq (a : Data) (Q r b : ℕ) :
    budget a Q r b =
      7 * ((a.stacks 252).length + (a.stacks 253).length +
        (a.stacks 272).length + (a.stacks 275).length + (a.stacks 284).length +
        (a.stacks 128).length + (a.stacks 254).length + (a.stacks 243).length +
        (a.stacks 133).length + (a.stacks 131).length) +
      Q * (7 * r + 14) + 48 * b + 81 := by
  simp only [budget, seedCost, seedSlots, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  simp +decide [source]
  ring

theorem command_eval (a : Data) (Q r R b : ℕ)
    (hempty : ∀ j, a.stacks (port j) = [])
    (hQ : a.stacks 253 = List.replicate Q true)
    (hr : a.stacks 252 = List.replicate r true)
    (hR : a.stacks 243 = List.replicate (R + 1) true)
    (hwidth : (a.stacks 129).length = b)
    (hzero : a.stacks 131 = List.replicate (4 * b) false) :
    ∃ out : Data, Eval command (budget a Q r b) a out ∧
      (∀ j, out.stacks (port j) = inputStacks a Q r R b j) ∧
      (∀ k, (¬ ∃ j, port j = k) → out.stacks k = a.stacks k) := by
  let a1 := seedResult seedSlots a
  let a2 := popped a1 R
  let a3 : Data := ⟨readRegs a2.regs 0 1 none,
    Function.update a2.stacks (port 30) (List.replicate b false)⟩
  let out : Data := ⟨(resetState a3).regs,
    Function.update a3.stacks (port 26) (List.replicate (Q * r) true)⟩
  have hseed := copySeeds_eval seedSlots a (by decide) (hempty 44)
  have hn (j : Fin 49) : a1.stacks (port j) = seedNative a j := seed_native a hempty j
  have hf (k : Fin 288) (hk : ∀ j, k ≠ port j) : a1.stacks k = a.stacks k :=
    seedResult_frame seedSlots a k (by intro j _; exact hk j)
  have hhigh (k : Fin 288) (hk : 128 ≤ k.val) : a1.stacks k = a.stacks k :=
    hf k (high_ne_port k hk)
  have hp := popRow_eval a1 R (by simpa +decide [seedNative, seedSlots, source] using (hn 32).trans hR)
  have hz := primeZero_eval a2 b
    (by simpa +decide [a2, popped, port, hhigh 131 (by decide)] using hzero)
    (by simpa +decide [a2, popped, port, hhigh 129 (by decide)] using hwidth)
    (by simpa +decide [a2, popped, port, seedNative, seedSlots] using hn 30)
    (by simpa +decide [a2, popped, port, seedNative, seedSlots] using hn 42)
    (by simpa +decide [a2, popped, port, seedNative, seedSlots] using hn 43)
    (by simpa +decide [a2, popped, port, seedNative, seedSlots] using hn 44)
  have hw := rowWidth_eval a3 Q r
    (by simpa +decide [a3, a2, popped, port, hhigh 253 (by decide)] using hQ)
    (by simpa +decide [a3, a2, popped, port, seedNative, seedSlots, source] using (hn 21).trans hr)
    (by simpa +decide [a3, a2, popped, port, seedNative, seedSlots] using hn 26)
    (by simpa +decide [a3, a2, popped, port, seedNative, seedSlots] using hn 15)
    (by simpa +decide [a3, a2, popped, port, seedNative, seedSlots] using hn 42)
    (by simpa +decide [a3, a2, popped, port, seedNative, seedSlots] using hn 44)
  refine ⟨out, ?_, ?_, ?_⟩
  · simpa only [command, budget, Nat.add_assoc] using hseed.seq (hp.seq (hz.seq hw))
  · intro j
    simp only [out, a3, a2, popped, inputStacks, Function.update_apply,
      port_injective.eq_iff, hn]
  · intro k hk
    have hn32 : k ≠ port 32 := fun h => hk ⟨32, h.symm⟩
    have hn30 : k ≠ port 30 := fun h => hk ⟨30, h.symm⟩
    have hn26 : k ≠ port 26 := fun h => hk ⟨26, h.symm⟩
    simp only [out, a3, a2, popped, Function.update_of_ne hn32,
      Function.update_of_ne hn30, Function.update_of_ne hn26]
    exact hf k (by intro j h; exact hk ⟨j, h.symm⟩)

abbrev program : Program 16 288 (size command + 1) := compiled command 272 (port 31)

/-- The control table does not depend on any source parameter. -/
theorem program_labels : size command + 1 = 133 := rfl

theorem program_run (a : Data) (Q r R b : ℕ)
    (hempty : ∀ j, a.stacks (port j) = [])
    (hQ : a.stacks 253 = List.replicate Q true)
    (hr : a.stacks 252 = List.replicate r true)
    (hR : a.stacks 243 = List.replicate (R + 1) true)
    (hwidth : (a.stacks 129).length = b)
    (hzero : a.stacks 131 = List.replicate (4 * b) false) :
    ∃ out : Data, RunsIn program (budget a Q r b + 1)
      (a.withPC (some program.entry)) (out.withPC none) ∧
      (∀ j, out.stacks (port j) = inputStacks a Q r R b j) ∧
      (∀ k, (¬ ∃ j, port j = k) → out.stacks k = a.stacks k) := by
  obtain ⟨out, he, hn, hf⟩ := command_eval a Q r R b hempty hQ hr hR hwidth hzero
  exact ⟨out, ⟨budget a Q r b + 1, le_rfl, compiled_halt_trace he 272 (port 31)⟩, hn, hf⟩

end SubexponentialSAT.Subexp.UniversalRowInputSetup

end OAI.Algorithms
