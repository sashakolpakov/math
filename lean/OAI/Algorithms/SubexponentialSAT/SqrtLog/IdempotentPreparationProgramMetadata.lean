import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramRepeat
import OAI.Algorithms.SubexponentialSAT.CounterConversions
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-! Literal cells, unary metadata and concrete zero-array allocation. Literal
lengths are fixed program syntax; all t-dependent repetitions use a runtime
unary counter and charge each bit copy. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev pushLiteral (target : Fin 41) (bit : Bool) : Cmd 8 41 :=
  .base (.seq (.atom (.set 0 bit)) (.atom (.push target 0)))

def pushedLiteral (d : Data) (target : Fin 41) (bit : Bool) : Data :=
  ⟨Function.update d.regs 0 bit, Function.update d.stacks target (bit :: d.stacks target)⟩

theorem pushLiteral_eval (d : Data) (target : Fin 41) (bit : Bool) :
    Eval (pushLiteral target bit) 2 d (pushedLiteral d target bit) := by
  exact .base ((StructuredProgram.Eval.atom (.set 0 bit) d).seq
    (StructuredProgram.Eval.atom (.push target 0) _))

def literalAt (target : Fin 41) : List Bool → Cmd 8 41
  | [] => .base .skip
  | b :: bs => .seq (literalAt target bs) (pushLiteral target b)

def literalResult (d : Data) (target : Fin 41) : List Bool → Data
  | [] => d
  | b :: bs => pushedLiteral (literalResult d target bs) target b

theorem literalAt_eval (d : Data) (target : Fin 41) (bits : List Bool) :
    Eval (literalAt target bits) (2*bits.length) d (literalResult d target bits) := by
  induction bits with
  | nil => exact .base (.skip _)
  | cons b bs ih =>
      convert ih.seq (pushLiteral_eval (literalResult d target bs) target b) using 1 <;>
        simp [literalAt, literalResult]

theorem literalResult_stacks (d : Data) (target : Fin 41) (bits : List Bool) :
    (literalResult d target bits).stacks =
      Function.update d.stacks target (bits ++ d.stacks target) := by
  induction bits with
  | nil => simp [literalResult]
  | cons b bs ih => simp [literalResult, pushedLiteral, ih, Function.update_idem]

abbrev clearAt (target : Fin 41) : Cmd 8 41 :=
  .call (StackRoutines.clearProgram target 0 1)

def clearResult (d : Data) (target : Fin 41) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks target []⟩

theorem clearAt_eval (d : Data) (target : Fin 41) :
    Eval (clearAt target) (2*(d.stacks target).length+3) d (clearResult d target) :=
  .call _ (ListRegisterProgram.clear_run target 0 1 d.regs d.stacks)

/-- Port 29 caches unary t; 0,1,2 are private scratch. The output port is a
fixed parameter of this finite program, not an input-dependent address. -/
abbrev copiesOfLiteral (target : Fin 41) (bits : List Bool) : Cmd 8 41 :=
  .seq (literalAt 0 bits) <|
  .seq (.call (StackRoutines.copyProgram 29 1 2 (0 : Fin 8) 1)) <|
  .seq (repeatAt 0 target 2 1) (clearAt 0)

theorem copiesOfLiteral_eval (d : Data) (target : Fin 41) (bits : List Bool)
    (n : ℕ) (hn : d.stacks 29 = List.replicate n true)
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = []) (h2 : d.stacks 2 = [])
    (ht0 : target ≠ 0) (ht1 : target ≠ 1) (ht2 : target ≠ 2) :
    ∃ rf, Eval (copiesOfLiteral target bits)
      (n*(7*bits.length+14)+4*bits.length+14) d
      ⟨rf, Function.update d.stacks target
        (Subexp.BlockCopyProgram.copies n bits ++ d.stacks target)⟩ := by
  let a := literalResult d 0 bits
  let b := afterCopy a 29 1 0 1
  let c := repeated b target 1 n bits
  have has : a.stacks = Function.update d.stacks 0 bits := by
    simp [a, literalResult_stacks, h0]
  have hbs : b.stacks = Function.update (Function.update d.stacks 0 bits) 1
      (List.replicate n true) := by
    simp [b, afterCopy, StackRoutines.copyStacks, has, hn, h1]
  have hcopy := copy_eval a 29 1 2 0 1 (by decide) (by decide) (by decide)
    (by decide) (by simp [has, h2])
  have hrep := repeatAt_eval b 0 target 2 1 (by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [repeatPorts, Ne.symm ht0, Ne.symm ht1, Ne.symm ht2])
    n (by simp [hbs]) (by simp [hbs, h2])
  have hrep' : Eval (repeatAt 0 target 2 1) (n*(7*bits.length+7)+6) b c := by
    simpa [hbs, c] using hrep
  have hclear := clearAt_eval c 0
  have hcs : c.stacks = Function.update (Function.update (Function.update d.stacks 0 bits) 1 [])
      target (Subexp.BlockCopyProgram.copies n bits ++ d.stacks target) := by
    simp [c, repeated, hbs, ht0, ht1, Function.update_idem]
  have hout : (clearResult c 0).stacks = Function.update d.stacks target
      (Subexp.BlockCopyProgram.copies n bits ++ d.stacks target) := by
    rw [clearResult, hcs]
    funext i
    by_cases hi0 : i = 0
    · subst i; simp [Ne.symm ht0, h0]
    · by_cases hi1 : i = 1
      · subst i; simp [Ne.symm ht1, h1]
      · by_cases hit : i = target
        · subst i; simp [ht0]
        · simp [hi0,hi1,hit]
  refine ⟨(clearResult c 0).regs, ?_⟩
  have he := (literalAt_eval d 0 bits).seq (hcopy.seq (hrep'.seq hclear))
  have hh : clearResult c 0 =
      ⟨(clearResult c 0).regs, Function.update d.stacks target
        (Subexp.BlockCopyProgram.copies n bits ++ d.stacks target)⟩ := state_ext rfl hout
  rw [hh] at he
  convert he using 1 ; simp [ has, hn, hcs, Ne.symm ht0] ; ring

abbrev metadataCommand : Cmd 8 41 :=
  .seq (copiesOfLiteral 12 [true,true]) (copiesOfLiteral 37 [true,true,true])

theorem metadataCommand_eval (d : Data) (t : ℕ)
    (ht : d.stacks 29 = List.replicate t true)
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = []) (h2 : d.stacks 2 = [])
    (h12 : d.stacks 12 = []) (h37 : d.stacks 37 = []) :
    ∃ rf, Eval metadataCommand (63*t+48) d
      ⟨rf, Function.update (Function.update d.stacks 12 (List.replicate (2*t) true))
        37 (List.replicate (3*t) true)⟩ := by
  obtain ⟨rf,ha⟩ := copiesOfLiteral_eval d 12 [true,true] t ht h0 h1 h2
    (by decide) (by decide) (by decide)
  let a : Data := ⟨rf, Function.update d.stacks 12 (List.replicate (2*t) true)⟩
  have ha' : Eval (copiesOfLiteral 12 [true,true]) (28*t+22) d a := by
    have hbits : Subexp.BlockCopyProgram.copies t [true,true] = List.replicate (2*t) true := by
      convert copies_replicate t 2 true using 1 <;> simp [Nat.mul_comm]
    simpa [a, hbits, h12, Nat.mul_comm] using ha
  obtain ⟨sf,hb⟩ := copiesOfLiteral_eval a 37 [true,true,true] t
    (by simp [a,ht]) (by simp [a,h0]) (by simp [a,h1]) (by simp [a,h2])
    (by decide) (by decide) (by decide)
  have hbits : Subexp.BlockCopyProgram.copies t [true,true,true] = List.replicate (3*t) true := by
    convert copies_replicate t 3 true using 1 <;> simp [Nat.mul_comm]
  refine ⟨sf, ?_⟩
  have he := ha'.seq hb
  convert he using 1 <;> simp [ a, hbits, h37] ; ring

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
