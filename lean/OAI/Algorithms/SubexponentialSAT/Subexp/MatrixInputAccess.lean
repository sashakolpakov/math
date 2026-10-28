import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms
import OAI.Algorithms.SubexponentialSAT.Subexp.CollisionStreamProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Fixed-port array access used to prepare the matrix-entry comparison. -/

namespace SubexponentialSAT.Subexp.MatrixInputAccess

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 8 29

def low : Fin 8 → Fin 29 := Fin.castAdd 21

theorem low_injective : Function.Injective low := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 29 => k.val) h)

abbrev read : Cmd 8 29 := .call
  (ProgramLinking.liftProgram (ArrayUpdatePrograms.readProgram (0 : Fin 8) 1) id low)

abbrev replace : Cmd 8 29 := .call
  (ProgramLinking.liftProgram (ArrayUpdatePrograms.replaceProgram (0 : Fin 8) 1) id low)

abbrev readResult (a : Data) (row : List Bool) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks 2 []) 1 (row ++ a.stacks 1)⟩

abbrev replaceResult (a : Data) (rows : List Bool) : Data :=
  ⟨readRegs a.regs 0 1 none, Function.update (Function.update a.stacks 2 []) 0 rows⟩

theorem embed_input (a : Data) :
    embedState id low a ⟨a.regs, a.stacks ∘ low⟩ = a := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id low_injective
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl

theorem read_eval (a : Data) (before : List (List Bool)) (row rest width : List Bool)
    (hs : a.stacks 0 = before.flatten ++ (row ++ rest))
    (hw : a.stacks 3 = width) (hi : (a.stacks 2).length = before.length)
    (hb : ∀ x ∈ before, x.length = width.length) (hr : row.length = width.length)
    (h4 : a.stacks 4 = []) (h5 : a.stacks 5 = [])
    (h6 : a.stacks 6 = []) (h7 : a.stacks 7 = []) :
    Eval read (before.length * (14 * width.length + 10) + 15 * width.length + 16)
      a (readResult a row) := by
  let b : State 8 8 := ⟨readRegs a.regs 0 1 none,
    ArrayUpdatePrograms.readStacks row (a.stacks ∘ low)⟩
  have ht := ArrayUpdatePrograms.readProgram_trace (0 : Fin 8) 1 (by decide)
    before row rest width (a.stacks 2) a.regs (a.stacks ∘ low)
    hs hw rfl hi hb hr h4 h5 h6 h7
  have he := eval_call_lifted (ArrayUpdatePrograms.readProgram (0 : Fin 8) 1)
    id low a Function.injective_id low_injective
    (a := ⟨a.regs, a.stacks ∘ low⟩) (b := b) ht
  have hf : embedState id low a b = readResult a row := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id low_injective
    · intro j; rfl
    · intro j hj; exact (hj ⟨j, rfl⟩).elim
    · intro j; fin_cases j <;> simp [ b, low, ArrayUpdatePrograms.readStacks]
    · intro j hj
      have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
      have h2 : j ≠ 2 := fun h => hj ⟨2, h.symm⟩
      simp [ h1, h2]
  simpa only [embed_input, hf, read] using he

theorem replace_eval (a : Data) (before : List (List Bool))
    (row newRow rest width : List Bool)
    (hs : a.stacks 0 = before.flatten ++ (row ++ rest))
    (hn : a.stacks 1 = newRow) (hw : a.stacks 3 = width)
    (hi : (a.stacks 2).length = before.length)
    (hb : ∀ x ∈ before, x.length = width.length)
    (hr : row.length = width.length) (hnew : newRow.length = width.length)
    (h4 : a.stacks 4 = []) (h5 : a.stacks 5 = [])
    (h6 : a.stacks 6 = []) (h7 : a.stacks 7 = []) :
    Eval replace (before.length * (14 * width.length + 10) + 20 * width.length + 21)
      a (replaceResult a (before.flatten ++ (newRow ++ rest))) := by
  let b : State 8 8 := ⟨readRegs a.regs 0 1 none,
    ArrayUpdatePrograms.replaceStacks before newRow rest (a.stacks ∘ low)⟩
  have ht := ArrayUpdatePrograms.replaceProgram_trace (0 : Fin 8) 1 (by decide)
    before row newRow rest width (a.stacks 2) a.regs (a.stacks ∘ low)
    hs hn hw rfl hi hb hr hnew h4 h5 h6 h7
  have he := eval_call_lifted (ArrayUpdatePrograms.replaceProgram (0 : Fin 8) 1)
    id low a Function.injective_id low_injective
    (a := ⟨a.regs, a.stacks ∘ low⟩) (b := b) ht
  have hf : embedState id low a b =
      replaceResult a (before.flatten ++ (newRow ++ rest)) := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id low_injective
    · intro j; rfl
    · intro j hj; exact (hj ⟨j, rfl⟩).elim
    · intro j; fin_cases j <;> simp [ b, low, ArrayUpdatePrograms.replaceStacks]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, h.symm⟩
      have h2 : j ≠ 2 := fun h => hj ⟨2, h.symm⟩
      simp [ h0, h2]
  simpa only [embed_input, hf, replace] using he

abbrev copy (src dst : Fin 29) : Cmd 8 29 := .call (copyProgram src dst 8 0 1)
abbrev copied (a : Data) (src dst : Fin 29) : Data :=
  ⟨readRegs a.regs 0 1 none, copyStacks src dst a.stacks⟩

theorem copy_eval (a : Data) (src dst : Fin 29) (hsd : src ≠ dst)
    (hs8 : src ≠ 8) (h8d : (8 : Fin 29) ≠ dst) (h8 : a.stacks 8 = []) :
    Eval (copy src dst) (7 * (a.stacks src).length + 5) a (copied a src dst) :=
  TupleProgram.copy_eval src dst 8 (0 : Fin 8) 1 hsd hs8 h8d (by decide) a h8

abbrev clear (src : Fin 29) : Cmd 8 29 := .call (clearProgram src 0 1)
abbrev cleared (a : Data) (src : Fin 29) : Data :=
  ⟨readRegs a.regs 0 1 none, clearStacks src a.stacks⟩

theorem clear_eval (a : Data) (src : Fin 29) :
    Eval (clear src) (2 * (a.stacks src).length + 3) a (cleared a src) := by
  apply Eval.call
  have h := halt_after_trace _ (clearProgram_trace src (0 : Fin 8) 1 a.regs a.stacks)
    2 rfl rfl
  simpa [clear, cleared, StructuredProgram.State.withPC, clearResult, clearProgram,
    Nat.add_assoc] using h

def eqRegs : Fin 5 → Fin 8 := Fin.castAdd 3
def eqPorts (j : Fin 13) : Fin 29 :=
  if j.val = 0 then 1 else if j.val = 1 then 0 else if j.val = 12 then 28 else Fin.castAdd 16 j

theorem eqRegs_injective : Function.Injective eqRegs := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 8 => k.val) h)

theorem eqPorts_injective : Function.Injective eqPorts := by
  decide

@[simp] theorem eqPorts_one : eqPorts 1 = 0 := rfl
@[simp] theorem eqPorts_eleven : eqPorts 11 = 11 := rfl
@[simp] theorem eqPorts_twelve : eqPorts 12 = 28 := rfl

def equalityInner := compiled CollisionStreamProgram.sealCommand (1 : Fin 13) 11
abbrev equality : Cmd 8 29 :=
  .seq (.call (ProgramLinking.liftProgram equalityInner eqRegs eqPorts))
    (.seq (.base (.atom (.pop 11 7 0))) (.base (.atom (.set 0 false))))

abbrev compared (a : Data) (answer : Bool) : Data :=
  ⟨fun j => if j = 7 then answer else if j.val < 5 then false else a.regs j,
    Function.update (Function.update a.stacks 0 []) 28 []⟩

theorem equality_eval (a : Data) (h11 : a.stacks 11 = []) :
    ∃ n ≤ 11 * (a.stacks 0).length + 2 * (a.stacks 28).length + 22,
      Eval equality n a (compared a (decide (a.stacks 0 = a.stacks 28))) := by
  let x : State 5 13 := ⟨a.regs ∘ eqRegs, a.stacks ∘ eqPorts⟩
  obtain ⟨n, hn, ht⟩ := CollisionStreamProgram.seal_eval x
  let y := CollisionStreamProgram.sealed x (decide (a.stacks 0 = a.stacks 28))
  let mid : Data :=
    ⟨fun j => if j.val < 5 then false else a.regs j,
      Function.update (Function.update (Function.update a.stacks 0 []) 28 [])
        11 [decide (a.stacks 0 = a.stacks 28)]⟩
  have hx : embedState eqRegs eqPorts a x = a := by
    apply embedState_eq_of_ports _ _ _ _ _ eqRegs_injective eqPorts_injective
    · intros; rfl
    · intros; rfl
    · intros; rfl
    · intros; rfl
  have hy : embedState eqRegs eqPorts a y = mid := by
    apply embedState_eq_of_ports _ _ _ _ _ eqRegs_injective eqPorts_injective
    · intro i
      change (if i.val < 5 then false else a.regs (eqRegs i)) = false
      simp [i.isLt]
    · intro j hj
      have hge : ¬ j.val < 5 := fun h => hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
      simp [mid, hge]
    · intro i
      by_cases hi1 : i = 1
      · subst i; simp [mid, y, x, CollisionStreamProgram.sealed, h11]
      by_cases hi12 : i = 12
      · subst i; simp [mid, y, x, CollisionStreamProgram.sealed, h11]
      by_cases hi11 : i = 11
      · subst i; simp [mid, y, x, CollisionStreamProgram.sealed, h11]
      have h0 : eqPorts i ≠ 0 := fun h => hi1 (eqPorts_injective (h.trans eqPorts_one.symm))
      have h28 : eqPorts i ≠ 28 := fun h => hi12 (eqPorts_injective (h.trans eqPorts_twelve.symm))
      have h11' : eqPorts i ≠ 11 := fun h => hi11 (eqPorts_injective (h.trans eqPorts_eleven.symm))
      simp [mid, y, x, CollisionStreamProgram.sealed, hi1, hi12, hi11, h0, h28, h11']
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨1, h.symm⟩
      have h28 : j ≠ 28 := fun h => hj ⟨12, h.symm⟩
      have h11' : j ≠ 11 := fun h => hj ⟨11, h.symm⟩
      simp [mid, h0, h28, h11']
  have ht' : Trace equalityInner (n + 1) (x.withPC (some equalityInner.entry))
      (y.withPC none) := by
    simpa [equalityInner, y, x, Function.comp_def, eqPorts] using
      compiled_halt_trace ht (1 : Fin 13) 11
  have hl := eval_call_lifted equalityInner eqRegs eqPorts a
    eqRegs_injective eqPorts_injective ht'
  have hl' : Eval (.call (ProgramLinking.liftProgram equalityInner eqRegs eqPorts))
      (n + 1) a mid := by
    simpa only [hx, hy] using hl
  have hf : (StructuredProgram.Atom.set (0 : Fin 8) false).eval
      ((StructuredProgram.Atom.pop (11 : Fin 29) 7 0).eval mid) =
      compared a (decide (a.stacks 0 = a.stacks 28)) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      by_cases hj0 : j = 0
      · subst j
        simp [mid, readRegs, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
      by_cases hj7 : j = 7
      · subst j
        simp [mid, readRegs, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
      simp [mid, readRegs, hj0, hj7, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]
    · funext j; by_cases hj : j = 11 <;>
        simp [mid, hj, h11, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
  have he := hl'.seq
    ((Eval.base (StructuredProgram.Eval.atom (.pop (11 : Fin 29) (7 : Fin 8) 0) mid)).seq
      (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 8) false)
        ((StructuredProgram.Atom.pop (11 : Fin 29) 7 0).eval mid))))
  rw [hf] at he
  refine ⟨n + 1 + (1 + 1), ?_, he⟩
  change n ≤ 11 * (a.stacks 0).length + 2 * (a.stacks 28).length + 19 at hn
  omega

end SubexponentialSAT.Subexp.MatrixInputAccess

end OAI.Algorithms
