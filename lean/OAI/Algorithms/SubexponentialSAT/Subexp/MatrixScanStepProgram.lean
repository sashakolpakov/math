import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixColorReadProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixPositionCountProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! One physical scan iteration: read four equal-width color records,
classify their same/swapped relation, and clear the consumed color buffers. -/

namespace SubexponentialSAT.Subexp.MatrixScanStepProgram

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 8 23

def lowPorts : Fin 17 → Fin 23 := Fin.castAdd 6

theorem lowPorts_injective : Function.Injective lowPorts := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 23 => k.val) h

def restrict (a : Data) : MatrixPositionProgram.Data :=
  ⟨a.regs, fun j => a.stacks (lowPorts j)⟩

def frame (base : Data) (a : MatrixPositionProgram.Data) : Data :=
  ⟨a.regs, fun j => if h : j.val < 17 then a.stacks ⟨j.val, h⟩ else base.stacks j⟩

theorem embed_eq_frame (base : Data) (a : MatrixPositionProgram.Data) :
    embedState id lowPorts base a = frame base a := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id lowPorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; simp [frame, lowPorts, i.isLt]
  · intro i hi
    have h : ¬ i.val < 17 := by
      intro h
      exact hi ⟨⟨i.val, h⟩, Fin.ext rfl⟩
    simp [frame, h]

theorem frame_restrict (a : Data) : frame a (restrict a) = a := by
  apply MatrixProgramSupport.data_ext
  · rfl
  · funext j
    by_cases h : j.val < 17
    · simp [frame, restrict, lowPorts]
    · simp [frame, h]

abbrev classify : Cmd 8 23 := .call
  (ProgramLinking.liftProgram MatrixPositionCountProgram.program id lowPorts)

def classified (a : Data) : Data :=
  frame a (MatrixPositionCountProgram.classified (restrict a))

theorem classify_eval (a : Data)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = [])
    (h11 : a.stacks 11 = []) (h12 : a.stacks 12 = []) :
    ∃ n ≤ 36 * MatrixPositionProgram.volume (restrict a) + 91,
      Eval classify n a (classified a) := by
  obtain ⟨n, hn, ht⟩ := MatrixPositionCountProgram.program_runsIn (restrict a) h0 h1 h11 h12
  have he := eval_call_lifted MatrixPositionCountProgram.program id lowPorts a
    Function.injective_id lowPorts_injective ht
  rw [embed_eq_frame, embed_eq_frame, frame_restrict] at he
  exact ⟨n, hn, he⟩

abbrev clear (i : Fin 23) : Cmd 8 23 := .call (clearProgram i 0 1)

def clearedOne (a : Data) (i : Fin 23) : Data :=
  ⟨readRegs a.regs 0 1 none, clearStacks i a.stacks⟩

theorem clear_eval (a : Data) (i : Fin 23) :
    Eval (clear i) (2 * (a.stacks i).length + 3) a (clearedOne a i) :=
  TupleProgram.clear_eval i (0 : Fin 8) 1 a

abbrev clearWords : Cmd 8 23 := .seq (clear 13) (.seq (clear 14) (.seq (clear 15) (clear 16)))

def cleared (a : Data) : Data :=
  clearedOne (clearedOne (clearedOne (clearedOne a 13) 14) 15) 16

theorem clearWords_eval (a : Data) :
    Eval clearWords (2 * MatrixPositionProgram.volume (restrict a) + 12) a (cleared a) := by
  have h0 := clear_eval a 13
  have h1 := clear_eval (clearedOne a 13) 14
  have h2 := clear_eval (clearedOne (clearedOne a 13) 14) 15
  have h3 := clear_eval (clearedOne (clearedOne (clearedOne a 13) 14) 15) 16
  have he := h0.seq (h1.seq (h2.seq h3))
  convert he using 1
  all_goals simp [cleared, clearedOne, clearStacks,
    MatrixPositionProgram.volume, restrict, lowPorts] <;> ring

abbrev command : Cmd 8 23 :=
  .seq MatrixColorReadProgram.pullFour (.seq classify clearWords)

def output (a : Data) (words rests : Fin 4 → List Bool) : Data :=
  cleared (classified (MatrixColorReadProgram.fourPulled a words rests))

theorem command_eval (a : Data) (words rests : Fin 4 → List Bool)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = []) (h4 : a.stacks 4 = [])
    (h10 : a.stacks 10 = []) (h11 : a.stacks 11 = []) (h12 : a.stacks 12 = [])
    (hd : ∀ i, a.stacks (MatrixColorReadProgram.target i) = [])
    (hs : ∀ i, a.stacks (MatrixColorReadProgram.source i) = words i ++ rests i)
    (hlen : ∀ i, (words i).length = (a.stacks 21).length) :
    ∃ n ≤ 208 * (a.stacks 21).length + 147,
      Eval command n a (output a words rests) := by
  have hp := MatrixColorReadProgram.pullFour_eval a words rests h0 h4 h10 hd hs hlen
  let b := MatrixColorReadProgram.fourPulled a words rests
  obtain ⟨nc, hnc, hc⟩ := classify_eval b
    (by simp [b, h0])
    (by simp [b, h1])
    (by simp [b, h11])
    (by simp [b, h12])
  have hclear := clearWords_eval (classified b)
  have hvol : MatrixPositionProgram.volume (restrict b) = 4 * (a.stacks 21).length := by
    change (b.stacks 13).length + (b.stacks 14).length +
      (b.stacks 15).length + (b.stacks 16).length = _
    have h13 : b.stacks 13 = words 0 := rfl
    have h14 : b.stacks 14 = words 1 := rfl
    have h15 : b.stacks 15 = words 2 := rfl
    have h16 : b.stacks 16 = words 3 := rfl
    rw [h13, h14, h15, h16, hlen 0, hlen 1, hlen 2, hlen 3]
    omega
  have hvol' : MatrixPositionProgram.volume (restrict (classified b)) =
      MatrixPositionProgram.volume (restrict b) := by
    change ((classified b).stacks 13).length + ((classified b).stacks 14).length +
      ((classified b).stacks 15).length + ((classified b).stacks 16).length =
      (b.stacks 13).length + (b.stacks 14).length + (b.stacks 15).length + (b.stacks 16).length
    have hc13 : (classified b).stacks 13 = b.stacks 13 := rfl
    have hc14 : (classified b).stacks 14 = b.stacks 14 := rfl
    have hc15 : (classified b).stacks 15 = b.stacks 15 := rfl
    have hc16 : (classified b).stacks 16 = b.stacks 16 := rfl
    rw [hc13, hc14, hc15, hc16]
  refine ⟨56 * (a.stacks 21).length + 44 +
    (nc + (2 * MatrixPositionProgram.volume (restrict (classified b)) + 12)), ?_,
    hp.seq (hc.seq hclear)⟩
  rw [hvol] at hnc
  rw [hvol', hvol]
  omega

end SubexponentialSAT.Subexp.MatrixScanStepProgram

end OAI.Algorithms
