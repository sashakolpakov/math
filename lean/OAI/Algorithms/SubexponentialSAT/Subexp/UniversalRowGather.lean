import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms
import OAI.Algorithms.SubexponentialSAT.Subexp.GatherProgram
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-!
# Reading actual scalar and difference-row data for universal rows

All tables are packed runtime arrays. The selected index is unary data on
stack 16. The three fixed reads preserve their source tables and index and
produce the correction scalar, inverse node, and complete difference row.
-/

namespace SubexponentialSAT.Subexp.UniversalRowGather

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 8 32
abbrev Word := List Bool

inductive Field where
  | value | inverse | difference
  deriving DecidableEq

def arrayPort : Field → Fin 32
  | .value => 24
  | .inverse => 25
  | .difference => 27

def outputPort : Field → Fin 32
  | .value => 19
  | .inverse => 20
  | .difference => 0

def widthPort : Field → Fin 32
  | .value | .inverse => 29
  | .difference => 30

def readPorts (field : Field) : Fin 8 → Fin 32 :=
  ![arrayPort field, outputPort field, 2, widthPort field, 4, 5, 6, 7]

theorem readPorts_injective (field : Field) : Function.Injective (readPorts field) := by
  cases field <;> decide

abbrev read (field : Field) : Cmd 8 32 :=
  .call (ProgramLinking.liftProgram (ArrayUpdatePrograms.readProgram (0 : Fin 8) 1)
    id (readPorts field))

abbrev readIndex (field : Field) : Cmd 8 32 :=
  .seq (.call (copyProgram 16 2 15 (0 : Fin 8) 1)) (read field)

def result (field : Field) (a : Data) (word : Word) : Data :=
  ⟨readRegs a.regs 0 1 none, Function.update a.stacks (outputPort field) word⟩

/-- Each read has a fixed port map. Table widths and the selected position
are consumed only as runtime words by the existing array-access program. -/
theorem readIndex_eval (field : Field) (rows : List Word) (width index : Word) (a : Data)
    (harray : a.stacks (arrayPort field) = rows.flatten)
    (hwidth : a.stacks (widthPort field) = width) (hindex : a.stacks 16 = index)
    (hi : index.length < rows.length)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hout : a.stacks (outputPort field) = [])
    (h2 : a.stacks 2 = []) (h4 : a.stacks 4 = []) (h5 : a.stacks 5 = [])
    (h6 : a.stacks 6 = []) (h7 : a.stacks 7 = []) (h15 : a.stacks 15 = []) :
    Eval (readIndex field) (index.length * (14 * width.length + 17) + 15 * width.length + 21)
      a (result field a (rows.getD index.length [])) := by
  let copied := SubexpScanPrimitives.afterCopy a 16 2 0 1
  have hc := SubexpScanPrimitives.copy_eval a 16 2 15 0 1
    (by decide) (by decide) (by decide) (by decide) h15
  let inner : State 8 8 := ⟨copied.regs, copied.stacks ∘ readPorts field⟩
  have htake : (rows.take index.length).length = index.length := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hrow : (rows.getD index.length []).length = width.length := by
    rw [List.getD_eq_getElem _ _ hi]
    exact hrows _ (List.getElem_mem hi)
  have hs : inner.stacks 0 = (rows.take index.length).flatten ++
      (rows.getD index.length [] ++ (rows.drop (index.length + 1)).flatten) := by
    have ha : inner.stacks 0 = rows.flatten := by
      cases field <;> simpa [inner, copied, SubexpScanPrimitives.afterCopy,
        copyStacks, readPorts, arrayPort] using harray
    exact ha.trans (GatherProgram.row_decomposition rows _ hi)
  have hw : inner.stacks 3 = width := by
    cases field <;> simpa [inner, copied, SubexpScanPrimitives.afterCopy,
      copyStacks, readPorts, widthPort] using hwidth
  have hidx : inner.stacks 2 = index := by
    simp [inner, copied, SubexpScanPrimitives.afterCopy, copyStacks, readPorts, hindex, h2]
  have ht := ArrayUpdatePrograms.readProgram_trace (0 : Fin 8) 1 (by decide)
    (rows.take index.length) (rows.getD index.length [])
    (rows.drop (index.length + 1)).flatten width index inner.regs inner.stacks
    hs hw hidx htake.symm (fun row hr => hrows row (List.mem_of_mem_take hr)) hrow
    (by simp [inner, copied, SubexpScanPrimitives.afterCopy, copyStacks, readPorts, h4])
    (by simp [inner, copied, SubexpScanPrimitives.afterCopy, copyStacks, readPorts, h5])
    (by simp [inner, copied, SubexpScanPrimitives.afterCopy, copyStacks, readPorts, h6])
    (by simp [inner, copied, SubexpScanPrimitives.afterCopy, copyStacks, readPorts, h7])
  have hin : embedState id (readPorts field) copied inner = copied := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id (readPorts_injective field)
    · intros; rfl
    · intros; rfl
    · intros; rfl
    · intros; rfl
  have hend : embedState id (readPorts field) copied
      ⟨readRegs inner.regs 0 1 none,
        ArrayUpdatePrograms.readStacks (rows.getD index.length []) inner.stacks⟩ =
      result field a (rows.getD index.length []) := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id (readPorts_injective field)
    · intro j; simp [result, inner, copied, SubexpScanPrimitives.afterCopy, readRegs_reset]
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro j
      cases field <;> fin_cases j <;>
        simp_all [result, inner, copied, SubexpScanPrimitives.afterCopy, copyStacks,
          readPorts, arrayPort, outputPort, widthPort, ArrayUpdatePrograms.readStacks]
    · intro j hj
      have ho : j ≠ outputPort field := fun h => hj ⟨1, h.symm⟩
      have hidx : j ≠ 2 := fun h => hj ⟨2, h.symm⟩
      simp [result, copied, SubexpScanPrimitives.afterCopy, copyStacks, ho, hidx]
  have hr := eval_call_lifted (ArrayUpdatePrograms.readProgram (0 : Fin 8) 1)
    id (readPorts field) copied Function.injective_id (readPorts_injective field)
    (a := inner) (b := ⟨readRegs inner.regs 0 1 none,
      ArrayUpdatePrograms.readStacks (rows.getD index.length []) inner.stacks⟩) ht
  rw [hin, hend] at hr
  have run := hc.seq hr
  convert run using 1
  simp [ hindex, htake]
  ring

abbrev termFields : Cmd 8 32 :=
  .seq (readIndex .value) (.seq (readIndex .inverse) (readIndex .difference))

def termResult (a : Data) (value inverse differenceRow : Word) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update (Function.update a.stacks 19 value) 20 inverse) 0 differenceRow⟩

theorem termFields_eval (values inverses differences : List Word)
    (width rowWidth index : Word) (a : Data)
    (hv : a.stacks 24 = values.flatten) (hinv : a.stacks 25 = inverses.flatten)
    (hdiff : a.stacks 27 = differences.flatten)
    (hw : a.stacks 29 = width) (hrw : a.stacks 30 = rowWidth) (hi : a.stacks 16 = index)
    (hvi : index.length < values.length) (hii : index.length < inverses.length)
    (hdi : index.length < differences.length)
    (hvs : ∀ row ∈ values, row.length = width.length)
    (his : ∀ row ∈ inverses, row.length = width.length)
    (hds : ∀ row ∈ differences, row.length = rowWidth.length)
    (h0 : a.stacks 0 = []) (h19 : a.stacks 19 = []) (h20 : a.stacks 20 = [])
    (h2 : a.stacks 2 = []) (h4 : a.stacks 4 = []) (h5 : a.stacks 5 = [])
    (h6 : a.stacks 6 = []) (h7 : a.stacks 7 = []) (h15 : a.stacks 15 = []) :
    Eval termFields
      (index.length * (28 * width.length + 14 * rowWidth.length + 51) +
        30 * width.length + 15 * rowWidth.length + 63)
      a (termResult a (values.getD index.length []) (inverses.getD index.length [])
        (differences.getD index.length [])) := by
  let a1 := result .value a (values.getD index.length [])
  let a2 := result .inverse a1 (inverses.getD index.length [])
  have h1 := readIndex_eval .value values width index a hv hw hi hvi hvs h19
    h2 h4 h5 h6 h7 h15
  have h2' := readIndex_eval .inverse inverses width index a1
    (by simpa [a1, result, outputPort, arrayPort] using hinv)
    (by simpa [a1, result, outputPort, widthPort] using hw)
    (by simpa [a1, result, outputPort] using hi) hii his
    (by simpa [a1, result, outputPort] using h20)
    (by simpa [a1, result, outputPort] using h2)
    (by simpa [a1, result, outputPort] using h4)
    (by simpa [a1, result, outputPort] using h5)
    (by simpa [a1, result, outputPort] using h6)
    (by simpa [a1, result, outputPort] using h7)
    (by simpa [a1, result, outputPort] using h15)
  have h3 := readIndex_eval .difference differences rowWidth index a2
    (by simpa [a2, a1, result, outputPort, arrayPort] using hdiff)
    (by simpa [a2, a1, result, outputPort, widthPort] using hrw)
    (by simpa [a2, a1, result, outputPort] using hi) hdi hds
    (by simpa [a2, a1, result, outputPort] using h0)
    (by simpa [a2, a1, result, outputPort] using h2)
    (by simpa [a2, a1, result, outputPort] using h4)
    (by simpa [a2, a1, result, outputPort] using h5)
    (by simpa [a2, a1, result, outputPort] using h6)
    (by simpa [a2, a1, result, outputPort] using h7)
    (by simpa [a2, a1, result, outputPort] using h15)
  have ht := h1.seq (h2'.seq h3)
  convert ht using 1
  · ring
  · simp [termResult, a2, a1, result, outputPort, readRegs_reset]

end SubexponentialSAT.Subexp.UniversalRowGather

end OAI.Algorithms
