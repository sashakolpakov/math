import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixInputAccess

namespace OAI.Algorithms

/-! Read the selected color from each of four preserved word streams. The
position is a unary runtime cursor on stack37; color width is on stack21. -/

namespace SubexponentialSAT.Subexp.MatrixAnchorReadProgram

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 10 42

def low : Fin 8 → Fin 42 := Fin.castAdd 34
theorem low_injective : Function.Injective low := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 42 => k.val) h)

abbrev read : Cmd 10 42 := .call
  (ProgramLinking.liftProgram (ArrayUpdatePrograms.readProgram (0 : Fin 10) 1) id low)

def readResult (a : Data) (row : List Bool) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks 2 []) 1 (row ++ a.stacks 1)⟩

theorem read_eval (a : Data) (before : List (List Bool)) (row rest width : List Bool)
    (hs : a.stacks 0 = before.flatten ++ (row ++ rest))
    (hw : a.stacks 3 = width) (hi : (a.stacks 2).length = before.length)
    (hb : ∀ x ∈ before, x.length = width.length) (hr : row.length = width.length)
    (h4 : a.stacks 4 = []) (h5 : a.stacks 5 = [])
    (h6 : a.stacks 6 = []) (h7 : a.stacks 7 = []) :
    Eval read (before.length * (14 * width.length + 10) + 15 * width.length + 16)
      a (readResult a row) := by
  let b : State 10 8 := ⟨readRegs a.regs 0 1 none,
    ArrayUpdatePrograms.readStacks row (a.stacks ∘ low)⟩
  have ht := ArrayUpdatePrograms.readProgram_trace (0 : Fin 10) 1 (by decide)
    before row rest width (a.stacks 2) a.regs (a.stacks ∘ low)
    hs hw rfl hi hb hr h4 h5 h6 h7
  have he := eval_call_lifted (ArrayUpdatePrograms.readProgram (0 : Fin 10) 1)
    id low a Function.injective_id low_injective
    (a := ⟨a.regs, a.stacks ∘ low⟩) (b := b) ht
  have hin : embedState id low a ⟨a.regs, a.stacks ∘ low⟩ = a := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id low_injective <;> intros <;> rfl
  have hout : embedState id low a b = readResult a row := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id low_injective
    · intro j; rfl
    · intro j hj; exact (hj ⟨j, rfl⟩).elim
    · intro j; fin_cases j <;> simp [readResult, b, low, ArrayUpdatePrograms.readStacks]
    · intro j hj
      have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
      have h2 : j ≠ 2 := fun h => hj ⟨2, h.symm⟩
      simp [readResult, h1, h2]
  simpa only [hin, hout, read] using he

abbrev copy (src dst : Fin 42) : Cmd 10 42 := .call (copyProgram src dst 8 0 1)
def copied (a : Data) (src dst : Fin 42) : Data :=
  ⟨readRegs a.regs 0 1 none, copyStacks src dst a.stacks⟩
theorem copy_eval (a : Data) (src dst : Fin 42) (hsd : src ≠ dst)
    (hs8 : src ≠ 8) (h8d : (8 : Fin 42) ≠ dst) (h8 : a.stacks 8 = []) :
    Eval (copy src dst) (7 * (a.stacks src).length + 5) a (copied a src dst) :=
  TupleProgram.copy_eval src dst 8 (0 : Fin 10) 1 hsd hs8 h8d (by decide) a h8

abbrev transfer (src dst : Fin 42) : Cmd 10 42 := .call (transferProgram src dst 0 1)
def transferred (a : Data) (src dst : Fin 42) : Data :=
  ⟨readRegs a.regs 0 1 none, transferStacks src dst a.stacks⟩
theorem transfer_eval (a : Data) (src dst : Fin 42) (hsd : src ≠ dst) :
    Eval (transfer src dst) (3 * (a.stacks src).length + 3) a (transferred a src dst) :=
  TupleProgram.transfer_eval src dst (0 : Fin 10) 1 hsd (by decide) a

abbrev move (src dst : Fin 42) : Cmd 10 42 := .seq (transfer src 8) (transfer 8 dst)
def moved (a : Data) (src dst : Fin 42) : Data := transferred (transferred a src 8) 8 dst
theorem move_eval (a : Data) (src dst : Fin 42) (hs8 : src ≠ 8)
    (h8d : (8 : Fin 42) ≠ dst) (h8 : a.stacks 8 = []) :
    Eval (move src dst) (6 * (a.stacks src).length + 6) a (moved a src dst) := by
  have he := (transfer_eval a src 8 hs8).seq (transfer_eval (transferred a src 8) 8 dst h8d)
  convert he using 1
  all_goals simp [moved, transferred, transferStacks, h8] <;> omega

abbrev clear (src : Fin 42) : Cmd 10 42 := .call (clearProgram src 0 1)
def cleared (a : Data) (src : Fin 42) : Data :=
  ⟨readRegs a.regs 0 1 none, clearStacks src a.stacks⟩
theorem clear_eval (a : Data) (src : Fin 42) :
    Eval (clear src) (2 * (a.stacks src).length + 3) a (cleared a src) :=
  TupleProgram.clear_eval src (0 : Fin 10) 1 a

def source (i : Fin 4) : Fin 42 := ⟨17 + i.val, by omega⟩
def target (i : Fin 4) : Fin 42 := ⟨38 + i.val, by omega⟩

abbrev readOne (i : Fin 4) : Cmd 10 42 :=
  .seq (copy (source i) 0) (.seq (copy 21 3) (.seq (copy 37 2)
    (.seq read (.seq (move 1 (target i)) (.seq (clear 0) (clear 3))))))

def readOneResult (a : Data) (i : Fin 4) (row : List Bool) : Data :=
  ⟨readRegs a.regs 0 1 none, Function.update a.stacks (target i) row⟩

theorem readOne_eval (a : Data) (i : Fin 4) (before : List (List Bool)) (row rest : List Bool)
    (hwork : ∀ j : Fin 42, j.val < 9 → a.stacks j = [])
    (hd : a.stacks (target i) = [])
    (hs : a.stacks (source i) = before.flatten ++ (row ++ rest))
    (hi : (a.stacks 37).length = before.length)
    (hb : ∀ x ∈ before, x.length = (a.stacks 21).length)
    (hr : row.length = (a.stacks 21).length) :
    Eval (readOne i)
      (9 * (a.stacks (source i)).length + before.length * (14 * (a.stacks 21).length + 17) +
        30 * (a.stacks 21).length + 43) a (readOneResult a i row) := by
  have hw0 := hwork 0 (by decide)
  have hw1 := hwork 1 (by decide)
  have hw2 := hwork 2 (by decide)
  have hw3 := hwork 3 (by decide)
  have hw4 := hwork 4 (by decide)
  have hw5 := hwork 5 (by decide)
  have hw6 := hwork 6 (by decide)
  have hw7 := hwork 7 (by decide)
  have hw8 := hwork 8 (by decide)
  let a1 := copied a (source i) 0
  let a2 := copied a1 21 3
  let a3 := copied a2 37 2
  let a4 := readResult a3 row
  let a5 := moved a4 1 (target i)
  let a6 := cleared a5 0
  let a7 := cleared a6 3
  have t0 := copy_eval a (source i) 0
    (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by decide) (hwork 8 (by decide))
  have t1 := copy_eval a1 21 3 (by decide) (by decide) (by decide)
    (by fin_cases i <;> simp +decide [a1, copied, copyStacks, source, hw8])
  have t2 := copy_eval a2 37 2 (by decide) (by decide) (by decide)
    (by fin_cases i <;> simp +decide [a2, a1, copied, copyStacks, source, hw8])
  have t3 := read_eval a3 before row rest (a.stacks 21)
    (by fin_cases i <;> simpa +decide [a3, a2, a1, copied, copyStacks, source, hw0] using hs)
    (by fin_cases i <;> simp +decide [a3, a2, a1, copied, copyStacks, source, hw3])
    (by fin_cases i <;> simpa +decide [a3, a2, a1, copied, copyStacks, source, hw2] using hi)
    hb hr
    (by fin_cases i <;> simp +decide [a3, a2, a1, copied, copyStacks, source, hw4])
    (by fin_cases i <;> simp +decide [a3, a2, a1, copied, copyStacks, source, hw5])
    (by fin_cases i <;> simp +decide [a3, a2, a1, copied, copyStacks, source, hw6])
    (by fin_cases i <;> simp +decide [a3, a2, a1, copied, copyStacks, source, hw7])
  have t4 := move_eval a4 1 (target i) (by decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> simp +decide [a4, a3, a2, a1, readResult, copied, copyStacks, source, hw8])
  have t5 := clear_eval a5 0
  have t6 := clear_eval a6 3
  have hf : a7 = readOneResult a i row := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      fin_cases j <;>
        simp [ a6, a5, a4, a3, a2, a1, cleared, moved,
          transferred, readResult, copied, readRegs]
    · funext j
      fin_cases i <;> fin_cases j <;>
        simp +decide [ a6, a5, a4, a3, a2, a1, cleared, moved,
          transferred, readResult, copied, clearStacks, transferStacks, copyStacks,
          source, target, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8] at hd ⊢
      all_goals first | exact hd
  change cleared a6 3 = readOneResult a i row at hf
  have he := t0.seq (t1.seq (t2.seq (t3.seq (t4.seq (t5.seq t6)))))
  rw [hf] at he
  convert he using 1
  fin_cases i <;>
    simp +decide [a6, a5, a4, a3, a2, a1, readResult, cleared, moved, transferred,
      copied, clearStacks, transferStacks, copyStacks, source, target,
      hw0, hw1, hw2, hw3, hw8, hr, hi]
    <;> ring

end SubexponentialSAT.Subexp.MatrixAnchorReadProgram

end OAI.Algorithms
