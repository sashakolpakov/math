import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCopyProgram
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.SubexpParameterProgram

namespace OAI.Algorithms

/-! Native runtime-sized cell repetition for idempotent preparation. The
source cell and unary count are data; the finite control is independent of
both lengths. Every source bit copied into the destination is charged. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 8 41

def repeatRegisters : Fin 3 → Fin 8 := Fin.castAdd 5

theorem repeatRegisters_injective : Function.Injective repeatRegisters := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin 8 => x.val) h

def repeatPorts (source target scratch count : Fin 41) : Fin 4 → Fin 41 :=
  ![source, target, scratch, count]

abbrev resetThree : Cmd 8 41 := .base (SubexpParameterProgram.atoms
  [.set 0 false, .set 1 false, .set 2 false])

def resetData (d : Data) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 false) 2 false,
    d.stacks⟩

theorem resetThree_eval (d : Data) : Eval resetThree 3 d (resetData d) := by
  exact .base (SubexpParameterProgram.atoms_eval _ d)

abbrev repeatAt (source target scratch count : Fin 41) : Cmd 8 41 :=
  .seq resetThree (.call (ProgramLinking.liftProgram Subexp.BlockCopyProgram.program
    repeatRegisters (repeatPorts source target scratch count)))

def repeated (d : Data) (target count : Fin 41) (n : ℕ) (cell : List Bool) : Data :=
  ⟨(resetData d).regs, Function.update (Function.update d.stacks count []) target
    (Subexp.BlockCopyProgram.copies n cell ++ d.stacks target)⟩

theorem repeatAt_eval (d : Data) (source target scratch count : Fin 41)
    (distinct : Function.Injective (repeatPorts source target scratch count))
    (n : ℕ) (hc : d.stacks count = List.replicate n true)
    (hs : d.stacks scratch = []) :
    Eval (repeatAt source target scratch count)
      (n * (7 * (d.stacks source).length + 7) + 6) d
      (repeated d target count n (d.stacks source)) := by
  let a := resetData d
  let ports := repeatPorts source target scratch count
  have hst : source ≠ target := distinct.ne (by decide : (0 : Fin 4) ≠ 1)
  have hsc : source ≠ count := distinct.ne (by decide : (0 : Fin 4) ≠ 3)
  have htc : target ≠ count := distinct.ne (by decide : (1 : Fin 4) ≠ 3)
  have hts : scratch ≠ target := distinct.ne (by decide : (2 : Fin 4) ≠ 1)
  have hcs : scratch ≠ count := distinct.ne (by decide : (2 : Fin 4) ≠ 3)
  have hi : embedState repeatRegisters ports a
      (Subexp.BlockCopyProgram.initialState n (d.stacks source) (d.stacks target)) = a := by
    apply embedState_eq _ _ repeatRegisters_injective distinct
    · intro i
      fin_cases i <;> simp [a, resetData, repeatRegisters,
        Subexp.BlockCopyProgram.initialState, Subexp.BlockCopyProgram.data]
    · intro i
      fin_cases i <;> simp [a, resetData, repeatPorts,
        Subexp.BlockCopyProgram.initialState, Subexp.BlockCopyProgram.data, hc, hs]
    · intros; rfl
    · intros; rfl
  have ho : embedState repeatRegisters ports a
      (Subexp.BlockCopyProgram.data false false (d.stacks source)
        (Subexp.BlockCopyProgram.copies n (d.stacks source) ++ d.stacks target) []) =
      repeated d target count n (d.stacks source) := by
    apply embedState_eq _ _ repeatRegisters_injective distinct
    · intro i
      fin_cases i <;> simp [repeated, resetData, repeatRegisters,
        Subexp.BlockCopyProgram.data]
    · intro i
      fin_cases i <;> simp [repeated, repeatPorts,
        Subexp.BlockCopyProgram.data, hst, hsc, htc.symm, hts, hcs, hs]
    · intro i hi
      exact rfl
    · intro i hi
      have hit : i ≠ target := fun h => hi ⟨1, by simpa [ports, repeatPorts] using h.symm⟩
      have hic : i ≠ count := fun h => hi ⟨3, by simpa [ports, repeatPorts] using h.symm⟩
      simp [repeated, a, resetData, hit, hic]
  have he := eval_call_lifted Subexp.BlockCopyProgram.program repeatRegisters ports a
    repeatRegisters_injective distinct
    (Subexp.BlockCopyProgram.program_trace n (d.stacks source) (d.stacks target))
  rw [hi, ho] at he
  convert (resetThree_eval d).seq he using 1 ; try rfl
  omega

theorem copies_replicate (n width : ℕ) (bit : Bool) :
    Subexp.BlockCopyProgram.copies n (List.replicate width bit) =
      List.replicate (n * width) bit := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Subexp.BlockCopyProgram.copies_succ, ih, ← List.replicate_add]
      congr 1
      ring

/-- Filling an array from one scalar cell has a concrete linear bit trace. -/
theorem repeatAt_zero_eval (d : Data) (source target scratch count : Fin 41)
    (distinct : Function.Injective (repeatPorts source target scratch count))
    (n width : ℕ) (hc : d.stacks count = List.replicate n true)
    (hs : d.stacks scratch = []) (hz : d.stacks source = List.replicate width false)
    (ht : d.stacks target = []) :
    Eval (repeatAt source target scratch count) (n * (7 * width + 7) + 6) d
      ⟨(resetData d).regs, Function.update (Function.update d.stacks count []) target
        (List.replicate (n * width) false)⟩ := by
  simpa [repeated, hz, ht, copies_replicate] using
    repeatAt_eval d source target scratch count distinct n hc hs

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
