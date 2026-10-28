import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowTermFraming

namespace OAI.Algorithms

/-! One actual correction-term iteration, from packed tables to a row record. -/

namespace SubexponentialSAT.Subexp.UniversalRowTermProgram

open BitProgram StructuredCalls StackRoutines
open UniversalRowGather (Data Word)
open UniversalRowFactorLoop (indexWord)

def indices (positions : List ℕ) : Word :=
  Encoding.encodeList id (positions.reverse.map indexWord)

structure Ready (values inverses negatives rows : List Word) (width rowWidth : Word)
    (positions : List ℕ) (i : ℕ) (a : Data) : Prop where
  values : a.stacks 24 = values.flatten
  inverses : a.stacks 25 = inverses.flatten
  negatives : a.stacks 26 = negatives.flatten
  rows : a.stacks 27 = rows.flatten
  indices : a.stacks 28 = indices positions
  width : a.stacks 29 = width
  rowWidth : a.stacks 30 = rowWidth
  index : a.stacks 16 = indexWord i
  empty : ∀ j : Fin 32,
    j ∈ [0, 1, 2, 4, 5, 6, 7, 8, 9, 11, 12, 15, 19, 20, 21, 22, 23] → a.stacks j = []

def term (values inverses negatives differences : List Word) (positions : List ℕ) (i : ℕ) :
    UniversalRowProgram.Term Word :=
  ⟨values.getD i [], inverses.getD i [],
    UniversalRowFactorLoop.factors differences negatives i positions⟩

abbrev command : Cmd 8 32 :=
  .seq UniversalRowGather.termFields
    (.seq (.call (copyProgram 28 8 15 (0 : Fin 8) 1))
      (.seq (TupleProgram.pushConst 21 0 false)
        (.seq UniversalRowFactorLoop.loop
          (.seq UniversalRowTermFraming.term
            (.seq (.call (clearProgram 0 (0 : Fin 8) 1))
              (.seq (.call (clearProgram 16 (0 : Fin 8) 1))
                UniversalRowFactorLoop.resetFlags))))))

def cost (values inverses negatives differences : List Word)
    (width rowWidth : Word) (positions : List ℕ) (i : ℕ) : ℕ :=
  i * (28 * width.length + 14 * rowWidth.length + 51) +
    30 * width.length + 15 * rowWidth.length + 63 +
    7 * (indices positions).length +
    RecordPrograms.budget (UniversalRowFactorLoop.callbackCost width.length i)
      (positions.reverse.map indexWord) +
    UniversalRowTermFraming.termCost (values.getD i []) (inverses.getD i [])
      (Encoding.encodeList UniversalRowProgram.encodeFactor
        (UniversalRowFactorLoop.factors differences negatives i positions)) +
    2 * rowWidth.length + 2 * i + 20

theorem command_eval (values inverses negatives rows differences : List Word)
    (width rowWidth : Word) (positions : List ℕ) (i : ℕ) (a : Data)
    (ha : Ready values inverses negatives rows width rowWidth positions i a)
    (hvi : i < values.length) (hii : i < inverses.length) (hri : i < rows.length)
    (hvs : ∀ row ∈ values, row.length = width.length)
    (his : ∀ row ∈ inverses, row.length = width.length)
    (hrs : ∀ row ∈ rows, row.length = rowWidth.length)
    (hds : ∀ row ∈ differences, row.length = width.length)
    (hns : ∀ row ∈ negatives, row.length = width.length)
    (hrow : rows.getD i [] = differences.flatten)
    (hpositions : ∀ j ∈ positions, j < differences.length ∧ j < negatives.length) :
    ∃ n ≤ cost values inverses negatives differences width rowWidth positions i,
      ∃ b : Data, Eval command n a b ∧
        b.regs 5 = false ∧ b.regs 6 = true ∧ b.regs 7 = false ∧
        b.stacks = Function.update (Function.update a.stacks 16 []) 31
          (true :: (Encoding.frame
            (UniversalRowProgram.encodeTerm (term values inverses negatives differences positions i)) ++
              a.stacks 31)) := by
  let a1 := UniversalRowGather.termResult a (values.getD i []) (inverses.getD i []) (rows.getD i [])
  have hfields := UniversalRowGather.termFields_eval values inverses rows width rowWidth (indexWord i) a
    ha.values ha.inverses ha.rows ha.width ha.rowWidth ha.index
    (by simpa using hvi) (by simpa using hii) (by simpa using hri) hvs his hrs
    (ha.empty 0 (by simp)) (ha.empty 19 (by simp)) (ha.empty 20 (by simp))
    (ha.empty 2 (by simp)) (ha.empty 4 (by simp)) (ha.empty 5 (by simp))
    (ha.empty 6 (by simp)) (ha.empty 7 (by simp)) (ha.empty 15 (by simp))
  simp only [UniversalRowFactorLoop.indexWord_length] at hfields
  let a2 : Data := ⟨readRegs a1.regs 0 1 none, copyStacks 28 8 a1.stacks⟩
  have hcopy := TupleProgram.copy_eval 28 8 15 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) a1
    (by simpa [a1, UniversalRowGather.termResult] using ha.empty 15 (by simp))
  let a3 := TupleProgram.pushedState (21 : Fin 32) (0 : Fin 8) false a2
  have hinit := TupleProgram.pushConst_eval (21 : Fin 32) (0 : Fin 8) false a2
  have hready : UniversalRowFactorLoop.Ready differences negatives width (indexWord i) a3 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact hrow
    · simpa [a3, a2, a1, TupleProgram.pushedState, UniversalRowGather.termResult, copyStacks]
        using ha.negatives
    · simpa [a3, a2, a1, TupleProgram.pushedState, UniversalRowGather.termResult, copyStacks]
        using ha.width
    · simpa [a3, a2, a1, TupleProgram.pushedState, UniversalRowGather.termResult, copyStacks]
        using ha.index
    · intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa [a3, a2, a1, TupleProgram.pushedState, UniversalRowGather.termResult, copyStacks]
          using ha.empty _ (by simp)
  have hacc : a3.stacks 21 = [false] := by
    simpa [a3, a2, a1, TupleProgram.pushedState, UniversalRowGather.termResult, copyStacks]
      using congrArg (List.cons false) (ha.empty 21 (by simp))
  obtain ⟨nl, hnl, next, hloop, hnext, hfactor, hframe⟩ :=
    UniversalRowFactorLoop.loop_indices_eval differences negatives width i positions [] a3
      hready hacc hds hns hpositions (a3.regs 5) (a3.regs 6) (a3.regs 7)
  have hstart : RecordPrograms.state UniversalRowFactorLoop.ports a3
      (a3.regs 5) (a3.regs 6) (a3.regs 7)
      (Encoding.encodeList id (positions.reverse.map indexWord) ++ []) [] = a3 := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simp [a3, a2, a1, UniversalRowGather.termResult, copyStacks,
        UniversalRowFactorLoop.ports, ha.indices, ha.empty 8 (by simp), indices]
    · simpa [a3, a2, a1, TupleProgram.pushedState, UniversalRowGather.termResult, copyStacks,
        UniversalRowFactorLoop.ports] using ha.empty 9 (by simp)
  rw [hstart] at hloop
  let a4 := RecordPrograms.state UniversalRowFactorLoop.ports next false true false [] []
  have h4 : a4.stacks = Function.update (Function.update a1.stacks 8 []) 21
      (Encoding.encodeList UniversalRowProgram.encodeFactor
        (UniversalRowFactorLoop.factors differences negatives i positions)) := by
    funext j
    by_cases hj8 : j = 8
    · subst j
      simp [a4, RecordPrograms.state, UniversalRowFactorLoop.ports]
    by_cases hj9 : j = 9
    · subst j
      simp [a4, RecordPrograms.state, UniversalRowFactorLoop.ports, a1,
        UniversalRowGather.termResult, ha.empty 9 (by simp)]
    by_cases hj21 : j = 21
    · subst j
      simpa [a4, RecordPrograms.state, UniversalRowFactorLoop.ports] using hfactor
    · have hf := hframe j hj21
      simp [a4, RecordPrograms.state, UniversalRowFactorLoop.ports, hj8, hj9, hj21,
        hf, a3, a2, copyStacks]
  obtain ⟨a5, hterm, h5⟩ := UniversalRowTermFraming.term_eval a4
    (values.getD i []) (inverses.getD i [])
    (UniversalRowFactorLoop.factors differences negatives i positions)
    (by simp [h4, a1, UniversalRowGather.termResult])
    (by simp [h4, a1, UniversalRowGather.termResult])
    (by simp [h4])
    (by simpa [h4, a1, UniversalRowGather.termResult] using ha.empty 23 (by simp))
  let a6 : Data := ⟨readRegs a5.regs 0 1 none, clearStacks 0 a5.stacks⟩
  let a7 : Data := ⟨readRegs a6.regs 0 1 none, clearStacks 16 a6.stacks⟩
  have hclear0 := TupleProgram.clear_eval 0 (0 : Fin 8) 1 a5
  have hclear16 := TupleProgram.clear_eval 16 (0 : Fin 8) 1 a6
  have hreset := UniversalRowFactorLoop.resetFlags_eval a7
  have hrun := hfields.seq (hcopy.seq (hinit.seq (hloop.seq
    (hterm.seq (hclear0.seq (hclear16.seq hreset))))))
  let b := UniversalRowFactorLoop.resetState a7
  have hrowsize : (rows.getD i []).length = rowWidth.length := by
    rw [List.getD_eq_getElem _ _ hri]
    exact hrs _ (List.getElem_mem hri)
  refine ⟨_, ?_, b, hrun, ?_, ?_, ?_, ?_⟩
  · have hc : a1.stacks 28 = indices positions := by
      simpa [a1, UniversalRowGather.termResult] using ha.indices
    have hzero : a5.stacks 0 = rows.getD i [] := by
      simp [h5, h4, a1, UniversalRowGather.termResult]
    have hi : a6.stacks 16 = indexWord i := by
      simpa [a6, clearStacks, h5, h4, a1, UniversalRowGather.termResult] using ha.index
    simp only [hc, hzero, hi, hrowsize, UniversalRowFactorLoop.indexWord_length]
    unfold cost
    omega
  · simp [b ]
  · simp [b ]
  · simp [b ]
  · funext j
    have he0 := ha.empty 0 (by simp)
    have he8 := ha.empty 8 (by simp)
    have he19 := ha.empty 19 (by simp)
    have he20 := ha.empty 20 (by simp)
    have he21 := ha.empty 21 (by simp)
    by_cases hj0 : j = 0
    · subst j; simp [b, a7, a6, clearStacks, h5, h4,
        a1, UniversalRowGather.termResult, he0]
    by_cases hj8 : j = 8
    · subst j; simp [b, a7, a6, clearStacks, h5, h4,
        a1, UniversalRowGather.termResult, he8]
    by_cases hj16 : j = 16
    · subst j; simp [b, a7, a6, clearStacks]
    by_cases hj19 : j = 19
    · subst j; simp [b, a7, a6, clearStacks, h5, h4,
        a1, UniversalRowGather.termResult, he19]
    by_cases hj20 : j = 20
    · subst j; simp [b, a7, a6, clearStacks, h5, h4,
        a1, UniversalRowGather.termResult, he20]
    by_cases hj21 : j = 21
    · subst j; simp [b, a7, a6, clearStacks, h5, h4,
        a1, UniversalRowGather.termResult, he21]
    by_cases hj31 : j = 31
    · subst j; simp [b, a7, a6, clearStacks, h5, h4,
        a1, UniversalRowGather.termResult, term]
    · simp [b, a7, a6, clearStacks, h5, h4,
        a1, UniversalRowGather.termResult, hj0, hj8, hj16, hj19, hj20, hj21, hj31]

end SubexponentialSAT.Subexp.UniversalRowTermProgram

end OAI.Algorithms
