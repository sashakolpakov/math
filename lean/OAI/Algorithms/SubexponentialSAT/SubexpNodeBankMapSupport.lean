import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixImageEnumeration
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Fixed-port operations used by the matrix-bundle-to-bank-list mapper. -/

namespace SubexponentialSAT.SubexpNodeBankMap

open BitProgram StructuredCalls SubexpScanPrimitives
open Subexp

abbrev Data := State 16 64
abbrev Code := Cmd 16 64

def highRegs (a b : Data) : Prop :=
  ∀ i : Fin 16, 13 ≤ i.val → b.regs i = a.regs i

theorem highRegs_refl (a : Data) : highRegs a a := by
  intro i hi
  rfl

theorem highRegs_trans {a b c : Data} (hab : highRegs a b) (hbc : highRegs b c) :
    highRegs a c := by
  intro i hi
  exact (hbc i hi).trans (hab i hi)

theorem readRegs_high (d : Data) (i : Fin 16) (hi : 13 ≤ i.val) :
    readRegs d.regs 0 1 none i = d.regs i := by
  have h0 : i ≠ 0 := by intro h; subst i; norm_num at hi
  have h1 : i ≠ 1 := by intro h; subst i; norm_num at hi
  simp [readRegs, h0, h1]

def transfer (src dst : Fin 64) : Code :=
  .call (StackRoutines.transferProgram src dst 0 1)

def copy (src dst : Fin 64) : Code :=
  .call (StackRoutines.copyProgram src dst 36 0 1)

def clear (src : Fin 64) : Code := .call (StackRoutines.clearProgram src 0 1)

def cleared (d : Data) (src : Fin 64) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

theorem transfer_eval (d : Data) (src dst : Fin 64) (h : src ≠ dst) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d
      (afterTransfer d src dst 0 1) :=
  SubexpScanPrimitives.transfer_eval d src dst 0 1 h (by decide)

theorem copy_eval (d : Data) (src dst : Fin 64) (hsd : src ≠ dst)
    (hs : src ≠ 36) (hd : (36 : Fin 64) ≠ dst) (ht : d.stacks 36 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d
      (afterCopy d src dst 0 1) :=
  SubexpScanPrimitives.copy_eval d src dst 36 0 1 hsd hs hd (by decide) ht

theorem clear_eval (d : Data) (src : Fin 64) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared d src) := by
  simpa only [clear, cleared, StackRoutines.clearStacks] using
    Subexp.TupleProgram.clear_eval src (0 : Fin 16) 1 d

def fieldPorts (src dst : Fin 64) (h : src ≠ dst) : RecordPrograms.Ports 16 64 :=
  ⟨0, 1, 2, src, dst, by decide, by decide, by decide, h⟩

def readWord (src dst : Fin 64) (h : src ≠ 36) : Code :=
  .seq (RecordPrograms.reader (fieldPorts src 36 h)) (transfer 36 dst)

def readResult (d : Data) (src dst : Fin 64) (bits tail : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update (Function.update d.stacks src tail) dst bits⟩

theorem readWord_eval (d : Data) (src dst : Fin 64)
    (hsd : src ≠ dst) (hs : src ≠ 36) (hd : (36 : Fin 64) ≠ dst)
    (bits tail : List Bool) (hsrc : d.stacks src = Encoding.frame bits ++ tail)
    (hdst : d.stacks dst = []) (htmp : d.stacks 36 = []) :
    Eval (readWord src dst hs) (9 * bits.length + 7) d
      (readResult d src dst bits tail) := by
  let p := fieldPorts src 36 hs
  let a := RecordPrograms.state p d false true (d.regs 2) tail bits.reverse
  have hin : RecordPrograms.state p d (d.regs 0) (d.regs 1) (d.regs 2)
      (Encoding.frame bits ++ tail) [] = d :=
    RecordPrograms.state_eq_self p d _ _ _ _ _ rfl rfl rfl hsrc htmp
  have hr := RecordPrograms.reader_eval p d bits tail []
    (d.regs 0) (d.regs 1) (d.regs 2)
  rw [hin] at hr
  simp only [List.append_nil] at hr
  have ht := transfer_eval a 36 dst hd
  have hlen : (a.stacks 36).length = bits.length := by
    simp [a, RecordPrograms.state, p, fieldPorts]
  have he : afterTransfer a 36 dst 0 1 = readResult d src dst bits tail := by
    apply state_ext
    · funext i
      by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> by_cases h2 : i = 2 <;>
        simp [afterTransfer, a, RecordPrograms.state, p, fieldPorts, readResult,
          readRegs, h0, h1, h2]
    · funext i
      by_cases hi : i = dst
      · subst i
        simp [afterTransfer, StackRoutines.transferStacks, a, RecordPrograms.state,
          p, fieldPorts, readResult, hdst, Ne.symm hd, Ne.symm hsd]
      · by_cases hi' : i = 36
        · subst i
          simp [afterTransfer, StackRoutines.transferStacks, a, RecordPrograms.state,
            p, fieldPorts, readResult, htmp, hd, Ne.symm hs]
        · simp [afterTransfer, StackRoutines.transferStacks, a, RecordPrograms.state,
            p, fieldPorts, readResult, hi, hi']
  have hh := hr.seq ht
  rw [he] at hh
  rw [hlen] at hh
  have hcost : (6 * bits.length + 4) + (3 * bits.length + 3) =
      9 * bits.length + 7 := by
    omega
  rw [hcost] at hh
  exact hh

def emitRecord (src dst : Fin 64) (hd : (36 : Fin 64) ≠ dst) : Code :=
  .seq (transfer src 36)
    (.seq (Subexp.TupleProgram.pushConst dst 0 false)
      (.seq (Subexp.TupleProgram.escape (fieldPorts 36 dst hd))
        (Subexp.TupleProgram.pushConst dst 0 true)))

def emitResult (d : Data) (src dst : Fin 64) : Data :=
  ⟨Function.update (readRegs d.regs 0 1 none) 0 true,
    Function.update (Function.update d.stacks src []) dst
      (Subexp.TupleProgram.prependRecord (d.stacks src) (d.stacks dst))⟩

theorem emitRecord_eval (d : Data) (src dst : Fin 64)
    (hsd : src ≠ dst) (hs : src ≠ 36) (hd : (36 : Fin 64) ≠ dst)
    (htmp : d.stacks 36 = []) :
    Eval (emitRecord src dst hd) (8 * (d.stacks src).length + 10) d
      (emitResult d src dst) := by
  let a := afterTransfer d src 36 0 1
  let b := Subexp.TupleProgram.pushedState dst 0 false a
  let c := Subexp.TupleProgram.escapedState (fieldPorts 36 dst hd) b
  have h1 := transfer_eval d src 36 hs
  have h2 := Subexp.TupleProgram.pushConst_eval dst (0 : Fin 16) false a
  have h3 := Subexp.TupleProgram.escape_eval_state (fieldPorts 36 dst hd) b
  have h4 := Subexp.TupleProgram.pushConst_eval dst (0 : Fin 16) true c
  have hlen : (b.stacks 36).length = (d.stacks src).length := by
    simp [b, a, afterTransfer, StackRoutines.transferStacks, htmp, hd]
  have he : Subexp.TupleProgram.pushedState dst 0 true c = emitResult d src dst := by
    apply state_ext
    · funext i
      by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
        simp [c, b, a, emitResult, fieldPorts, afterTransfer, readRegs, h0, h1]
    · funext i
      by_cases hi : i = dst
      · subst i
        simp [c, b, a, emitResult, fieldPorts, afterTransfer,
          StackRoutines.transferStacks, htmp, hd, Ne.symm hd, Ne.symm hsd,
          Subexp.TupleProgram.prependRecord, Subexp.TupleProgram.frame_eq_escaped,
          List.append_assoc]
      · by_cases hi' : i = src
        · subst i
          simp [c, b, a, emitResult, fieldPorts, afterTransfer,
            StackRoutines.transferStacks, htmp, hs, hi]
        · by_cases hi'' : i = 36
          · subst i
            simp [c, b, a, emitResult, fieldPorts, afterTransfer,
              StackRoutines.transferStacks, htmp, hd, Ne.symm hs]
          · simp [c, b, a, emitResult, fieldPorts, afterTransfer,
              StackRoutines.transferStacks, hi, hi', hi'']
  have hh := h1.seq (h2.seq (h3.seq h4))
  rw [he] at hh
  convert hh using 1 <;> (try simp only [emitRecord, fieldPorts, hlen]); omega

def matrixRegs : Fin 13 → Fin 16 := Fin.castAdd 3
def matrixStacks : Fin 32 → Fin 64 := Fin.castAdd 32

theorem matrixRegs_injective : Function.Injective matrixRegs := Fin.castAdd_injective _ _
theorem matrixStacks_injective : Function.Injective matrixStacks := Fin.castAdd_injective _ _

def enumerate : Code := .call (ProgramLinking.liftProgram
  MatrixImageEnumeration.program matrixRegs matrixStacks)

theorem enumerate_eval (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) (d : Data)
    (h : ∀ i, d.stacks (matrixStacks i) =
      (MatrixImageEnumeration.stored p M (d.regs ∘ matrixRegs) [] [] []).stacks i) :
    ∃ t ≤ MatrixImageEnumeration.sourceBudget p M, ∃ e,
      Eval enumerate t d e ∧ highRegs d e ∧
      e.stacks = Function.update d.stacks 22
        (ProgramEncoding.encodeRecords (MatrixImageEnumeration.bankRecords p M)) := by
  obtain ⟨rf, t, ht, he⟩ := MatrixImageEnumeration.program_run p M (d.regs ∘ matrixRegs)
  let a := MatrixImageEnumeration.stored p M (d.regs ∘ matrixRegs) [] [] []
  let b := MatrixImageEnumeration.stored p M rf [] []
    (ProgramEncoding.encodeRecords (MatrixImageEnumeration.bankRecords p M))
  let e := embedState matrixRegs matrixStacks d b
  have hin : embedState matrixRegs matrixStacks d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ matrixRegs_injective matrixStacks_injective
    · intro i; rfl
    · intros; rfl
    · exact h
    · intros; rfl
  have hh := eval_call_lifted MatrixImageEnumeration.program matrixRegs matrixStacks d
    matrixRegs_injective matrixStacks_injective he
  rw [hin] at hh
  refine ⟨t, ht, e, hh, ?_, ?_⟩
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega
  · funext i
    by_cases hi : ∃ j, matrixStacks j = i
    · obtain ⟨j, rfl⟩ := hi
      change (embedState matrixRegs matrixStacks d b).stacks (matrixStacks j) = _
      rw [embedState_stack _ _ _ _ matrixStacks_injective]
      by_cases hj : j = 22
      · subst j
        simp [b, MatrixImageEnumeration.stored, matrixStacks]
      · have hj' : matrixStacks j ≠ 22 := by
          intro heq
          apply hj
          apply Fin.ext
          have hv := congrArg (fun i : Fin 64 => i.val) heq
          exact hv
        rw [Function.update_of_ne hj', h]
        simp [b, MatrixImageEnumeration.stored, hj]
    · change (embedState matrixRegs matrixStacks d b).stacks i = _
      rw [embedState_stack_frame _ _ _ _ i hi]
      have hi' : i ≠ 22 := fun heq => hi ⟨22, heq.symm⟩
      exact (Function.update_of_ne hi' _ _).symm

end SubexponentialSAT.SubexpNodeBankMap

end OAI.Algorithms
