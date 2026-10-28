import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.Encoding

namespace OAI.Algorithms

/-! The raw natural-field reader. Its stopping delimiter is consumed, while
all subsequent fields and all other bank are preserved. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgramTupleCheck.Read
open SubexponentialSAT.BitProgram

abbrev program {r s : ℕ} (src dst : Fin s) (value present : Fin r) : Program r s 4 where
  inputStack := src
  outputStack := dst
  entry := 0
  code q := match q.val with
    | 0 => .pop src value present 1
    | 1 => .branch value 2 3
    | 2 => .push dst value 0
    | _ => .halt

def start {r s : ℕ} (regs : Fin r → Bool) (bank : Fin s → List Bool) : Cfg r s 4 :=
  ⟨some 0, regs, bank⟩

def finish {r s : ℕ} (src dst : Fin s) (value present : Fin r)
    (regs : Fin r → Bool) (bank : Fin s → List Bool) (n : ℕ) (tail : List Bool) : Cfg r s 4 :=
  ⟨none, readRegs regs value present (some false),
    Function.update (Function.update bank src tail) dst (List.replicate n true ++ bank dst)⟩

theorem zero {r s : ℕ} (src dst : Fin s) (value present : Fin r)
    (hvp : value ≠ present) (hsd : src ≠ dst)
    (regs : Fin r → Bool) (bank : Fin s → List Bool) (tail : List Bool)
    (hs : bank src = false :: tail) :
    Trace (program src dst value present) 3 (start regs bank)
      (finish src dst value present regs bank 0 tail) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, start, finish,
    hs, readRegs, hvp, Ne.symm hsd ]

theorem tick {r s : ℕ} (src dst : Fin s) (value present : Fin r)
    (hvp : value ≠ present) (hsd : src ≠ dst)
    (regs : Fin r → Bool) (bank : Fin s → List Bool) (tail : List Bool)
    (hs : bank src = true :: tail) :
    Trace (program src dst value present) 3 (start regs bank)
      (start (readRegs regs value present (some true))
        (Function.update (Function.update bank src tail) dst (true :: bank dst))) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, start,
    hs, readRegs, hvp, Ne.symm hsd]

theorem replicate_push (n : ℕ) (tail : List Bool) :
    List.replicate n true ++ true :: tail = true :: (List.replicate n true ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ] using congrArg (List.cons true) ih

theorem run {r s : ℕ} (src dst : Fin s) (value present : Fin r)
    (hvp : value ≠ present) (hsd : src ≠ dst)
    (regs : Fin r → Bool) (bank : Fin s → List Bool) (n : ℕ) (tail : List Bool)
    (hs : bank src = Encoding.encodeNat n ++ tail) :
    Trace (program src dst value present) (3 * n + 3) (start regs bank)
      (finish src dst value present regs bank n tail) := by
  induction n generalizing regs bank with
  | zero => exact zero src dst value present hvp hsd regs bank tail (by simpa [Encoding.encodeNat] using hs)
  | succ n ih =>
    have hs' : bank src = true :: (Encoding.encodeNat n ++ tail) := by
      simpa [Encoding.encodeNat, List.replicate_succ, List.append_assoc] using hs
    let mid := Function.update (Function.update bank src (Encoding.encodeNat n ++ tail)) dst
      (true :: bank dst)
    have ht := tick src dst value present hvp hsd regs bank _ hs'
    have hh := ih (readRegs regs value present (some true)) mid
      (by simp [mid, hsd])
    have hf : finish src dst value present (readRegs regs value present (some true)) mid n tail =
        finish src dst value present regs bank (n + 1) tail := by
      apply congrArg₂ (Cfg.mk none)
      · funext i; simp only [readRegs, Function.update_apply]; split_ifs <;> simp_all
      · funext i
        simp [ mid, Function.update_apply, List.replicate_succ]
        split_ifs <;> simp_all [replicate_push]
    rw [hf] at hh
    convert ht.trans hh using 1 ; omega
end SubexponentialSAT.SqrtLog.RowSelectionProgramTupleCheck.Read

end OAI.Algorithms
