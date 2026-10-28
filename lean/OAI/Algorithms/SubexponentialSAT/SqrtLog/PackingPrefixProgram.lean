import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPrepareCount
import OAI.Algorithms.SubexponentialSAT.Subexp.BasisTransposePlanProgram
import OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Paid prefix preparation. Raw unary inputs may contain arbitrary bits;
only their lengths matter. The persistent table and both counters survive. -/

namespace SubexponentialSAT.SqrtLog.PackingPrefixProgram

open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.Subexp

abbrev Data := State 3 11
abbrev unary (n : ℕ) := List.replicate n true

def normStack (out : Fin 11) : Fin 2 → Fin 11 := ![5,out]
abbrev normalize (out : Fin 11) : Cmd 3 11 :=
  .call (ProgramLinking.liftProgram PackingHeadProgramPrepareCount.program id (normStack out))

def afterNormalize (out : Fin 11) (a : Data) : Data :=
  ⟨fun _ => false, Function.update (Function.update a.stacks 5 []) out
    (unary (a.stacks 5).length ++ a.stacks out)⟩

theorem normalize_eval (out : Fin 11) (ho : out ≠ 5) (a : Data) :
    Eval (normalize out) (4 * (a.stacks 5).length + 4) a (afterNormalize out a) := by
  have hi : Function.Injective (normStack out) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [normStack]
  let b := PackingHeadProgramPrepareCount.state (fun _ => false) []
    (unary (a.stacks 5).length ++ a.stacks out)
  have ht := PackingHeadProgramPrepareCount.trace a.regs (a.stacks 5) (a.stacks out)
  have hs : PackingHeadProgramPrepareCount.state a.regs (a.stacks 5) (a.stacks out) =
      projectState id (normStack out) a := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> rfl
  rw [hs] at ht
  have he := eval_call_from_state PackingHeadProgramPrepareCount.program id (normStack out) a
    Function.injective_id hi ht
  have hb : embedState id (normStack out) a b = afterNormalize out a := by
    apply embedState_eq_of_ports id (normStack out) a _ _ Function.injective_id hi
    · intro i; rfl
    · intro i h; exact False.elim (h ⟨i,rfl⟩)
    · intro i; fin_cases i <;>
        simp [b, PackingHeadProgramPrepareCount.state, afterNormalize, normStack, Ne.symm ho]
    · intro i h
      have h5 : i ≠ 5 := fun hi => h ⟨0, by simpa [normStack] using hi.symm⟩
      have hout : i ≠ out := fun hi => h ⟨1, by simpa [normStack] using hi.symm⟩
      simp [afterNormalize, h5, hout]
  exact hb ▸ he

def mulStack : Fin 7 → Fin 11 := ![8,2,9,10,6,5,7]
theorem mulStack_injective : Function.Injective mulStack := by decide

abbrev multiply : Cmd 3 11 :=
  liftCommand BasisTransposePlanProgram.multiply 0 4 id mulStack

theorem multiply_eval (a : Data) (W h : ℕ)
    (hW : a.stacks 8 = unary W) (hh : a.stacks 5 = unary h) (htmp : a.stacks 7 = []) :
    ∃ n ≤ h * (7 * W + 7) + 3, ∃ regs : Fin 3 → Bool,
      Eval multiply n a ⟨regs,
        Function.update (Function.update a.stacks 5 []) 6 (unary (h * W) ++ a.stacks 6)⟩ := by
  let d := projectState id mulStack a
  obtain ⟨n, e, he, hn, hs⟩ := BasisTransposePlanProgram.multiply_eval W h d hW hh htmp
  have hl := eval_liftCommand_from_state BasisTransposePlanProgram.multiply 0 4 id mulStack a
    Function.injective_id mulStack_injective he
  let result : Data := ⟨e.regs,
    Function.update (Function.update a.stacks 5 []) 6 (unary (h * W) ++ a.stacks 6)⟩
  have hb : embedState id mulStack a e = result := by
    apply embedState_eq_of_ports id mulStack a _ _ Function.injective_id mulStack_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i
      rw [hs]
      fin_cases i <;> simp [result, d, projectState, mulStack, Function.comp_def, unary, BasisTransposePlanProgram.unary]
    · intro i hi
      have h5 : i ≠ 5 := fun h => hi ⟨5, by simpa [mulStack] using h.symm⟩
      have h6 : i ≠ 6 := fun h => hi ⟨4, by simpa [mulStack] using h.symm⟩
      simp [result, h5, h6]
  rw [hb] at hl
  exact ⟨n + 1, by omega, e.regs, hl⟩

def readStack : Fin 8 → Fin 11 := ![0,3,8,6,5,7,9,10]
theorem readStack_injective : Function.Injective readStack := by decide

abbrev readPrefix : Cmd 3 11 :=
  .call (ProgramLinking.liftProgram (ArrayUpdatePrograms.readProgram (0 : Fin 3) 1) id readStack)

theorem readPrefix_eval (a : Data) (size : ℕ)
    (hw : a.stacks 6 = unary size) (hlen : size ≤ (a.stacks 0).length)
    (h5 : a.stacks 5 = []) (h7 : a.stacks 7 = []) (h8 : a.stacks 8 = [])
    (h9 : a.stacks 9 = []) (h10 : a.stacks 10 = []) :
    Eval readPrefix (15 * size + 16) a
      ⟨readRegs a.regs 0 1 none,
        Function.update a.stacks 3 ((a.stacks 0).take size ++ a.stacks 3)⟩ := by
  let d := projectState id readStack a
  let record := (a.stacks 0).take size
  let rest := (a.stacks 0).drop size
  have hrecord : record.length = (unary size).length := by
    simp [record, List.length_take, Nat.min_eq_left hlen]
  have he := ArrayUpdatePrograms.readProgram_trace (0 : Fin 3) 1 (by decide)
    [] record rest (unary size) [] d.regs d.stacks
    (by simp [d, projectState, readStack, record, rest]) hw h8 (by rfl) (by simp)
    hrecord h5 h7 h9 h10
  have hl := eval_call_from_state (ArrayUpdatePrograms.readProgram (0 : Fin 3) 1) id readStack a
    Function.injective_id readStack_injective
    (b := ⟨readRegs d.regs 0 1 none, ArrayUpdatePrograms.readStacks record d.stacks⟩) he
  let result : Data := ⟨readRegs a.regs 0 1 none,
    Function.update a.stacks 3 (record ++ a.stacks 3)⟩
  have hb : embedState id readStack a
      ⟨readRegs d.regs 0 1 none, ArrayUpdatePrograms.readStacks record d.stacks⟩ = result := by
    apply embedState_eq_of_ports id readStack a _ _ Function.injective_id readStack_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i
      fin_cases i <;> simp [result, d, projectState, readStack, ArrayUpdatePrograms.readStacks,
        Function.comp_def, h8]
    · intro i hi
      have h3 : i ≠ 3 := fun h => hi ⟨1, by simpa [readStack] using h.symm⟩
      simp [result, h3]
  simpa only [List.length_nil, zero_mul, zero_add, List.length_replicate, hb] using hl

end SubexponentialSAT.SqrtLog.PackingPrefixProgram

end OAI.Algorithms
