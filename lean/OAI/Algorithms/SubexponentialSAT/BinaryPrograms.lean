import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BinaryArithmetic
import OAI.Algorithms.SubexponentialSAT.BitProgram
import OAI.Algorithms.SubexponentialSAT.BitProgramCompile
import OAI.Algorithms.SubexponentialSAT.ProgramLinking
import OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace OAI.Algorithms

/-!
# Fixed-control programs for binary arithmetic

Operands, their widths, and moduli are data. None of the programs in this file
have a control-state set depending on an operand length or numeric parameter.
-/

namespace SubexponentialSAT.BinaryPrograms

open SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.Computation

/-- Carry generation using three gates after the shared input XOR. -/
def fastCarry (a b c : Bool) : Bool :=
  (a && b).xor ((a.xor b) && c)

theorem fastCarry_eq (a b c : Bool) : fastCarry a b c = carryBit a b c := by
  cases a <;> cases b <;> cases c <;> decide

theorem addCarry_nonempty (c : Bool) (xs ys : List Bool)
    (h : xs ≠ [] ∨ ys ≠ []) :
    addCarry c xs ys =
      sumBit (xs.headD false) (ys.headD false) c ::
        addCarry (fastCarry (xs.headD false) (ys.headD false) c) xs.tail ys.tail := by
  cases xs with
  | nil =>
      cases ys with
      | nil => simp at h
      | cons b ys => simp [addCarry, carryAdd, fastCarry_eq]
  | cons a xs =>
      cases ys <;> simp [addCarry, fastCarry_eq]

namespace Add

abbrev Regs := Fin 8 → Bool
abbrev Config := SubexponentialSAT.BitProgram.Cfg 8 3 13

/-- A constant finite program: it never inspects the numeric value or length
of an operand. Registers 0..7 are carry,a,b,present-a,present-b,t,u,v. -/
def program : SubexponentialSAT.BitProgram.Program 8 3 13 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 1 3 1
    | 1 => .pop 1 2 4 2
    | 2 => .branch 3 4 3
    | 3 => .branch 4 4 10
    | 4 => .bxor 5 1 2 5
    | 5 => .band 6 1 2 6
    | 6 => .band 7 5 0 7
    | 7 => .bxor 1 5 0 8
    | 8 => .bxor 0 6 7 9
    | 9 => .push 2 1 0
    | 10 => .branch 0 11 12
    | 11 => .push 2 0 12
    | _ => .halt

def stackState (xs ys out : List Bool) : Fin 3 → List Bool :=
  fun k => if k = 0 then xs else if k = 1 then ys else out

def cfg (pc : Option (Fin 13)) (r : Regs) (xs ys out : List Bool) : Config :=
  ⟨pc, r, stackState xs ys out⟩

@[simp] theorem stacks_zero (xs ys out : List Bool) : stackState xs ys out 0 = xs := rfl
@[simp] theorem stacks_one (xs ys out : List Bool) : stackState xs ys out 1 = ys := rfl
@[simp] theorem stacks_two (xs ys out : List Bool) : stackState xs ys out 2 = out := rfl

@[simp] theorem update_left (xs ys out next : List Bool) :
    Function.update (stackState xs ys out) 0 next = stackState next ys out := by
  funext k
  fin_cases k <;> simp [stackState]

@[simp] theorem update_right (xs ys out next : List Bool) :
    Function.update (stackState xs ys out) 1 next = stackState xs next out := by
  funext k
  fin_cases k <;> simp [stackState]

@[simp] theorem update_output (xs ys out next : List Bool) :
    Function.update (stackState xs ys out) 2 next = stackState xs ys next := by
  funext k
  fin_cases k <;> simp [stackState]

def readRegisters (r : Regs) (a b : Option Bool) : Regs :=
  SubexponentialSAT.BitProgram.readRegs (SubexponentialSAT.BitProgram.readRegs r 1 3 a) 2 4 b

def roundRegisters (r : Regs) (a b : Option Bool) : Regs :=
  let ra := readRegisters r a b
  let rt := Function.update ra 5 (ra 1 ^^ ra 2)
  let ru := Function.update rt 6 (rt 1 && rt 2)
  let rv := Function.update ru 7 (ru 5 && ru 0)
  let rs := Function.update rv 1 (rv 5 ^^ rv 0)
  Function.update rs 0 (rs 6 ^^ rs 7)

@[simp] theorem roundRegisters_carry (r : Regs) (a b : Option Bool) :
    roundRegisters r a b 0 = fastCarry (a.getD false) (b.getD false) (r 0) := by
  simp [roundRegisters, readRegisters, SubexponentialSAT.BitProgram.readRegs, fastCarry]

@[simp] theorem roundRegisters_sum (r : Regs) (a b : Option Bool) :
    roundRegisters r a b 1 = sumBit (a.getD false) (b.getD false) (r 0) := by
  simp [roundRegisters, readRegisters, SubexponentialSAT.BitProgram.readRegs, sumBit]

theorem round_left (r : Regs) (a : Bool) (xs ys out : List Bool) :
    Trace (SubexponentialSAT.BitProgram.step program) 9
      (cfg (some 0) r (a :: xs) ys out)
      (cfg (some 0) (roundRegisters r (some a) ys.head?)
        xs ys.tail (sumBit a (ys.headD false) (r 0) :: out)) := by
  apply Trace.of_iterate
  cases ys <;>
    simp [Function.iterate_succ_apply, SubexponentialSAT.BitProgram.step, SubexponentialSAT.BitProgram.execInstr,
      program, cfg, roundRegisters, readRegisters, SubexponentialSAT.BitProgram.readRegs, sumBit]

theorem round_right (r : Regs) (b : Bool) (ys out : List Bool) :
    Trace (SubexponentialSAT.BitProgram.step program) 10
      (cfg (some 0) r [] (b :: ys) out)
      (cfg (some 0) (roundRegisters r none (some b))
        [] ys (sumBit false b (r 0) :: out)) := by
  apply Trace.of_iterate
  simp [Function.iterate_succ_apply, SubexponentialSAT.BitProgram.step, SubexponentialSAT.BitProgram.execInstr,
    program, cfg, roundRegisters, readRegisters, SubexponentialSAT.BitProgram.readRegs, sumBit]

theorem finish (r : Regs) (out : List Bool) :
    SubexponentialSAT.BitProgram.RunsIn program 7 (cfg (some 0) r [] [] out)
      (cfg none (readRegisters r none none) [] []
        (if r 0 then true :: out else out)) := by
  cases hc : r 0 with
  | false =>
      refine ⟨6, by decide, ?_⟩
      apply Trace.of_iterate
      simp [Function.iterate_succ_apply, SubexponentialSAT.BitProgram.step, SubexponentialSAT.BitProgram.execInstr,
        program, cfg, readRegisters, SubexponentialSAT.BitProgram.readRegs, hc]
  | true =>
      refine ⟨7, le_rfl, ?_⟩
      apply Trace.of_iterate
      simp [Function.iterate_succ_apply, SubexponentialSAT.BitProgram.step, SubexponentialSAT.BitProgram.execInstr,
        program, cfg, readRegisters, SubexponentialSAT.BitProgram.readRegs, hc]

theorem run_right (r : Regs) (ys out : List Bool) :
    ∃ rf : Regs, SubexponentialSAT.BitProgram.RunsIn program (10 * (ys.length + 1))
      (cfg (some 0) r [] ys out)
      (cfg none rf [] [] ((carryAdd (r 0) ys).reverse ++ out)) := by
  induction ys generalizing r out with
  | nil =>
      refine ⟨readRegisters r none none, ?_⟩
      have h := (finish r out).mono (show 7 ≤ 10 * (([] : List Bool).length + 1) by decide)
      cases hc : r 0 <;> simpa [carryAdd, hc] using h
  | cons b ys ih =>
      obtain ⟨rf, hr⟩ := ih (roundRegisters r none (some b))
        (sumBit false b (r 0) :: out)
      have hs : SubexponentialSAT.BitProgram.RunsIn program 10
          (cfg (some 0) r [] (b :: ys) out)
          (cfg (some 0) (roundRegisters r none (some b))
            [] ys (sumBit false b (r 0) :: out)) :=
        ⟨10, le_rfl, round_right r b ys out⟩
      refine ⟨rf, ?_⟩
      have ht := hs.trans hr
      have hcost : 10 + 10 * (ys.length + 1) =
          10 * ((b :: ys).length + 1) := by simp; omega
      rw [hcost] at ht
      simpa [carryAdd, roundRegisters_carry, fastCarry_eq, List.reverse_cons,
        List.append_assoc] using ht

/-- A complete execution to the halted state, for arbitrary operand lengths. -/
theorem run (r : Regs) (xs ys out : List Bool) :
    ∃ rf : Regs, SubexponentialSAT.BitProgram.RunsIn program (10 * (max xs.length ys.length + 1))
      (cfg (some 0) r xs ys out)
      (cfg none rf [] [] ((addCarry (r 0) xs ys).reverse ++ out)) := by
  induction xs generalizing r ys out with
  | nil => simpa [addCarry] using run_right r ys out
  | cons a xs ih =>
      obtain ⟨rf, hr⟩ := ih (roundRegisters r (some a) ys.head?) ys.tail
        (sumBit a (ys.headD false) (r 0) :: out)
      have hs : SubexponentialSAT.BitProgram.RunsIn program 10
          (cfg (some 0) r (a :: xs) ys out)
          (cfg (some 0) (roundRegisters r (some a) ys.head?)
            xs ys.tail (sumBit a (ys.headD false) (r 0) :: out)) :=
        ⟨9, by decide, round_left r a xs ys out⟩
      refine ⟨rf, ?_⟩
      have ht := hs.trans hr
      have hcost : 10 + 10 * (max xs.length ys.tail.length + 1) =
          10 * (max (a :: xs).length ys.length + 1) := by
        cases ys <;> simp [max_add_add_right] <;> omega
      rw [hcost] at ht
      cases ys <;>
        simpa [addCarry, roundRegisters_carry, fastCarry_eq, List.reverse_cons,
          List.append_assoc, max_add_add_right] using ht

theorem run_value (xs ys : List Bool) :
    ∃ rf : Regs, ∃ output : List Bool,
      BinaryArithmetic.toNat output.reverse = BinaryArithmetic.toNat xs + BinaryArithmetic.toNat ys ∧
      SubexponentialSAT.BitProgram.RunsIn program (10 * (max xs.length ys.length + 1))
        (cfg (some 0) (fun _ => false) xs ys [])
        (cfg none rf [] [] output) := by
  obtain ⟨rf, h⟩ := run (fun _ => false) xs ys []
  refine ⟨rf, (add xs ys).reverse, ?_, ?_⟩
  · simp
  · simpa [add] using h

/-- The complete adder followed by an actual stack-transfer loop.  Its output
has the same little-endian orientation as its inputs. -/
def littleEndianProgram : SubexponentialSAT.BitProgram.Program 8 3 17 :=
  SubexponentialSAT.ProgramLinking.link program
    (SubexponentialSAT.StackRoutines.transferProgram (2 : Fin 3) 0 (1 : Fin 8) 3)

theorem littleEndian_run (r : Regs) (xs ys : List Bool) :
    ∃ rf : Regs, SubexponentialSAT.BitProgram.RunsIn littleEndianProgram
      (16 * (max xs.length ys.length + 1))
      ⟨some 0, r, stackState xs ys []⟩
      ⟨none, rf, stackState (addCarry (r 0) xs ys) [] []⟩ := by
  obtain ⟨rf, hr⟩ := run r xs ys []
  let word := addCarry (r 0) xs ys
  let reverseProgram :=
    SubexponentialSAT.StackRoutines.transferProgram (2 : Fin 3) 0 (1 : Fin 8) 3
  have ht := SubexponentialSAT.StackRoutines.transferProgram_trace (2 : Fin 3) 0 (1 : Fin 8) 3
    (by decide) (by decide) rf (stackState [] [] word.reverse)
  have hh := SubexponentialSAT.StackRoutines.halt_after_trace reverseProgram ht 3 rfl rfl
  have hs : SubexponentialSAT.BitProgram.RunsIn reverseProgram (3 * word.length + 3)
      (SubexponentialSAT.ProgramLinking.enter reverseProgram (cfg none rf [] [] word.reverse))
      ⟨none, SubexponentialSAT.BitProgram.readRegs rf 1 3 none, stackState word [] []⟩ := by
    refine ⟨3 * word.reverse.length + 2 + 1, by simp, ?_⟩
    simpa [SubexponentialSAT.StackRoutines.transferResult, SubexponentialSAT.StackRoutines.transferStacks,
      SubexponentialSAT.ProgramLinking.enter, cfg, reverseProgram,
      SubexponentialSAT.StackRoutines.transferProgram] using hh
  have hr' : SubexponentialSAT.BitProgram.RunsIn program (10 * (max xs.length ys.length + 1))
      (cfg (some 0) r xs ys []) (cfg none rf [] [] word.reverse) := by
    simpa [word] using hr
  have hc := SubexponentialSAT.ProgramLinking.link_runsIn program reverseProgram hr' rfl hs
  have hlen := length_addCarry (r 0) xs ys
  refine ⟨SubexponentialSAT.BitProgram.readRegs rf 1 3 none, ?_⟩
  apply SubexponentialSAT.Computation.RunsIn.mono ?_ (show
      10 * (max xs.length ys.length + 1) + (3 * word.length + 3) ≤
        16 * (max xs.length ys.length + 1) by dsimp [word]; omega)
  simpa [littleEndianProgram, reverseProgram, SubexponentialSAT.ProgramLinking.relabelCfg,
    SubexponentialSAT.ProgramLinking.relocatePc, SubexponentialSAT.StackRoutines.transferProgram, cfg] using hc

theorem littleEndian_value (xs ys : List Bool) :
    ∃ rf : Regs, ∃ output : List Bool,
      BinaryArithmetic.toNat output = BinaryArithmetic.toNat xs + BinaryArithmetic.toNat ys ∧
      SubexponentialSAT.BitProgram.RunsIn littleEndianProgram (16 * (max xs.length ys.length + 1))
        ⟨some 0, (fun _ => false), stackState xs ys []⟩
        ⟨none, rf, stackState output [] []⟩ := by
  obtain ⟨rf, hr⟩ := littleEndian_run (fun _ => false) xs ys
  exact ⟨rf, add xs ys, toNat_add xs ys, hr⟩

/-- A primitive tape execution, with one fixed compilation factor. -/
theorem primitive_value (xs ys : List Bool) :
    ∃ rf : Regs, ∃ output : List Bool,
      BinaryArithmetic.toNat output = BinaryArithmetic.toNat xs + BinaryArithmetic.toNat ys ∧
      SubexponentialSAT.Computation.RunsIn (SubexponentialSAT.BitProgram.primitive littleEndianProgram).step
        (SubexponentialSAT.BitProgram.primitiveOverhead littleEndianProgram *
          (16 * (max xs.length ys.length + 1)))
        (SubexponentialSAT.BitProgram.primitiveCfg littleEndianProgram
          ⟨some 0, (fun _ => false), stackState xs ys []⟩)
        (SubexponentialSAT.BitProgram.primitiveCfg littleEndianProgram
          ⟨none, rf, stackState output [] []⟩) := by
  obtain ⟨rf, output, hv, hr⟩ := littleEndian_value xs ys
  exact ⟨rf, output, hv, SubexponentialSAT.BitProgram.primitive_execution littleEndianProgram hr⟩

end Add

namespace Mul

/-- The accumulator specification matched by the fixed-control multiplier. -/
def accumulate : List Bool → List Bool → List Bool → List Bool
  | [], _, acc => acc
  | b :: bs, ys, acc =>
      accumulate bs (false :: ys) (if b then add acc ys else acc)

theorem accumulate_value (xs ys acc : List Bool) :
    BinaryArithmetic.toNat (accumulate xs ys acc) = BinaryArithmetic.toNat acc + BinaryArithmetic.toNat xs * BinaryArithmetic.toNat ys := by
  induction xs generalizing ys acc with
  | nil => simp [accumulate]
  | cons b bs ih =>
      cases b <;> simp [accumulate, ih] <;> ring

theorem accumulate_length (xs ys acc : List Bool) :
    (accumulate xs ys acc).length ≤ max acc.length ys.length + xs.length := by
  induction xs generalizing ys acc with
  | nil => simp [accumulate]
  | cons b bs ih =>
      have hi := ih (false :: ys) (if b then add acc ys else acc)
      cases b with
      | false =>
          simp only [accumulate, Bool.false_eq_true, ↓reduceIte, List.length_cons] at *
          omega
      | true =>
          have ha := length_add acc ys
          simp only [accumulate, ↓reduceIte, List.length_cons] at *
          omega

abbrev Regs := Fin 8 → Bool
abbrev Config := SubexponentialSAT.BitProgram.Cfg 8 6 32

/-- The six ports are multiplier, shifted multiplicand, accumulator, copy,
copy scratch, and reversed sum. Every instruction acts on Boolean data only. -/
def program : SubexponentialSAT.BitProgram.Program 8 6 32 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 1 3 1
    | 1 => .branch 3 2 29
    | 2 => .branch 1 3 27
    | 3 => .pop 1 1 3 4
    | 4 => .branch 3 5 6
    | 5 => .push 4 1 3
    | 6 => .pop 4 1 3 7
    | 7 => .branch 3 8 10
    | 8 => .push 1 1 9
    | 9 => .push 3 1 6
    | 10 => .set 0 false 11
    | 11 => .pop 2 1 3 12
    | 12 => .pop 3 2 4 13
    | 13 => .branch 3 15 14
    | 14 => .branch 4 15 21
    | 15 => .bxor 5 1 2 16
    | 16 => .band 6 1 2 17
    | 17 => .band 7 5 0 18
    | 18 => .bxor 1 5 0 19
    | 19 => .bxor 0 6 7 20
    | 20 => .push 5 1 11
    | 21 => .branch 0 22 23
    | 22 => .push 5 0 23
    | 23 => .goto 24
    | 24 => .pop 5 1 3 25
    | 25 => .branch 3 26 27
    | 26 => .push 2 1 24
    | 27 => .set 1 false 28
    | 28 => .push 1 1 0
    | 29 => .pop 1 1 3 30
    | 30 => .branch 3 29 31
    | _ => .halt

def stackState (xs ys acc cp tmp rev : List Bool) : Fin 6 → List Bool :=
  ![xs, ys, acc, cp, tmp, rev]

@[simp] theorem stack_0 (xs ys acc cp tmp rev : List Bool) :
    stackState xs ys acc cp tmp rev 0 = xs := rfl
@[simp] theorem stack_1 (xs ys acc cp tmp rev : List Bool) :
    stackState xs ys acc cp tmp rev 1 = ys := rfl
@[simp] theorem stack_2 (xs ys acc cp tmp rev : List Bool) :
    stackState xs ys acc cp tmp rev 2 = acc := rfl
@[simp] theorem stack_3 (xs ys acc cp tmp rev : List Bool) :
    stackState xs ys acc cp tmp rev 3 = cp := rfl
@[simp] theorem stack_4 (xs ys acc cp tmp rev : List Bool) :
    stackState xs ys acc cp tmp rev 4 = tmp := rfl
@[simp] theorem stack_5 (xs ys acc cp tmp rev : List Bool) :
    stackState xs ys acc cp tmp rev 5 = rev := rfl

def cfg (pc : Option (Fin 32)) (r : Regs) (xs ys acc cp tmp rev : List Bool) : Config :=
  ⟨pc, r, stackState xs ys acc cp tmp rev⟩

def loopCfg (r : Regs) (xs ys acc : List Bool) : Config :=
  cfg (some 0) r xs ys acc [] [] []

@[simp] theorem update_0 (xs ys acc cp tmp rev next : List Bool) :
    Function.update (stackState xs ys acc cp tmp rev) 0 next =
      stackState next ys acc cp tmp rev := by
  funext k; fin_cases k <;> simp [stackState]

@[simp] theorem update_1 (xs ys acc cp tmp rev next : List Bool) :
    Function.update (stackState xs ys acc cp tmp rev) 1 next =
      stackState xs next acc cp tmp rev := by
  funext k; fin_cases k <;> simp [stackState]

@[simp] theorem update_2 (xs ys acc cp tmp rev next : List Bool) :
    Function.update (stackState xs ys acc cp tmp rev) 2 next =
      stackState xs ys next cp tmp rev := by
  funext k; fin_cases k <;> simp [stackState]

@[simp] theorem update_3 (xs ys acc cp tmp rev next : List Bool) :
    Function.update (stackState xs ys acc cp tmp rev) 3 next =
      stackState xs ys acc next tmp rev := by
  funext k; fin_cases k <;> simp [stackState]

@[simp] theorem update_4 (xs ys acc cp tmp rev next : List Bool) :
    Function.update (stackState xs ys acc cp tmp rev) 4 next =
      stackState xs ys acc cp next rev := by
  funext k; fin_cases k <;> simp [stackState]

@[simp] theorem update_5 (xs ys acc cp tmp rev next : List Bool) :
    Function.update (stackState xs ys acc cp tmp rev) 5 next =
      stackState xs ys acc cp tmp next := by
  funext k; fin_cases k <;> simp [stackState]

def addStack (k : Fin 3) : Fin 6 := ![2, 3, 5] k
def addLabel (k : Fin 13) : Fin 32 := ⟨k.val + 11, by omega⟩

theorem addStack_injective : Function.Injective addStack := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [addStack]

theorem add_code : SubexponentialSAT.ProgramLinking.CodeEmbedding Add.program program
    id addStack addLabel (some 24) := by
  intro q
  fin_cases q <;> rfl

theorem extend_addStack (xs ys acc cp tmp rev : List Bool) :
    Function.extend addStack (Add.stackState acc cp rev) (stackState xs ys [] [] tmp []) =
      stackState xs ys acc cp tmp rev := by
  funext k
  fin_cases k
  · rw [Function.extend_apply']
    · rfl
    · rintro ⟨a, ha⟩; fin_cases a <;> simp [addStack] at ha
  · rw [Function.extend_apply']
    · rfl
    · rintro ⟨a, ha⟩; fin_cases a <;> simp [addStack] at ha
  · exact addStack_injective.extend_apply _ _ (0 : Fin 3)
  · exact addStack_injective.extend_apply _ _ (1 : Fin 3)
  · rw [Function.extend_apply']
    · rfl
    · rintro ⟨a, ha⟩; fin_cases a <;> simp [addStack] at ha
  · exact addStack_injective.extend_apply _ _ (2 : Fin 3)

theorem embed_add (pc : Option (Fin 13)) (r rf : Regs)
    (xs ys acc cp tmp rev : List Bool) :
    SubexponentialSAT.ProgramLinking.embedCfg id addStack addLabel (some 24)
      (cfg (some 0) r xs ys [] [] tmp []) (Add.cfg pc rf acc cp rev) =
      cfg (SubexponentialSAT.ProgramLinking.relocatePc addLabel (some 24) pc)
        rf xs ys acc cp tmp rev := by
  simp [SubexponentialSAT.ProgramLinking.embedCfg, cfg, Add.cfg, extend_addStack]

/-- The adder is installed as literal instructions in this program's table. -/
theorem add_block (r : Regs) (xs ys acc cp tmp rev : List Bool) :
    ∃ rf : Regs, SubexponentialSAT.BitProgram.RunsIn program (10 * (max acc.length cp.length + 1))
      (cfg (some 11) r xs ys acc cp tmp rev)
      (cfg (some 24) rf xs ys [] [] tmp ((addCarry (r 0) acc cp).reverse ++ rev)) := by
  obtain ⟨rf, hr⟩ := Add.run r acc cp rev
  have ht := SubexponentialSAT.ProgramLinking.relocate_runsIn Add.program program
    id addStack addLabel (some 24) (cfg (some 0) r xs ys [] [] tmp [])
    Function.injective_id addStack_injective add_code hr
  refine ⟨rf, ?_⟩
  have hz : addLabel (0 : Fin 13) = (11 : Fin 32) := by
    apply Fin.ext
    simp [addLabel]
  simpa only [embed_add, SubexponentialSAT.ProgramLinking.relocatePc,
    hz] using ht

theorem copy_block (r : Regs) (xs ys acc : List Bool) :
    SubexponentialSAT.BitProgram.Trace program (7 * ys.length + 4)
      (cfg (some 3) r xs ys acc [] [] [])
      (cfg (some 10) (SubexponentialSAT.BitProgram.readRegs r 1 3 none) xs ys acc ys [] []) := by
  have h := SubexponentialSAT.StackRoutines.copy_trace program 1 3 4 1 3 3 4 5 6 7 8 9 10
    (by decide) (by decide) (by decide) (by decide)
    rfl rfl rfl rfl rfl rfl rfl r (stackState xs ys acc [] [] []) rfl
  simpa [SubexponentialSAT.StackRoutines.copyResult, SubexponentialSAT.StackRoutines.copyStacks, cfg] using h

theorem transfer_block (r : Regs) (xs ys word : List Bool) :
    SubexponentialSAT.BitProgram.Trace program (3 * word.length + 2)
      (cfg (some 24) r xs ys [] [] [] word.reverse)
      (cfg (some 27) (SubexponentialSAT.BitProgram.readRegs r 1 3 none) xs ys word [] [] []) := by
  have h := SubexponentialSAT.StackRoutines.transfer_trace program 5 2 1 3 24 25 26 27
    (by decide) (by decide) rfl rfl rfl r (stackState xs ys [] [] [] word.reverse)
  simpa [SubexponentialSAT.StackRoutines.transferResult, SubexponentialSAT.StackRoutines.transferStacks, cfg] using h

theorem enter_round (r : Regs) (b : Bool) (xs ys acc : List Bool) :
    SubexponentialSAT.BitProgram.Trace program 3 (loopCfg r (b :: xs) ys acc)
      (cfg (some (if b then 3 else 27))
        (SubexponentialSAT.BitProgram.readRegs r 1 3 (some b)) xs ys acc [] [] []) := by
  let r' := SubexponentialSAT.BitProgram.readRegs r 1 3 (some b)
  have h₁ : SubexponentialSAT.BitProgram.step program (loopCfg r (b :: xs) ys acc) =
      some (cfg (some 1) r' xs ys acc [] [] []) := by
    have h := SubexponentialSAT.BitProgram.step_code program (loopCfg r (b :: xs) ys acc)
      0 (.pop 0 1 3 1) rfl rfl
    simpa [SubexponentialSAT.BitProgram.execInstr, loopCfg, cfg, r'] using h
  have h₂ : SubexponentialSAT.BitProgram.step program (cfg (some 1) r' xs ys acc [] [] []) =
      some (cfg (some 2) r' xs ys acc [] [] []) := by
    have h := SubexponentialSAT.BitProgram.step_code program (cfg (some 1) r' xs ys acc [] [] [])
      1 (.branch 3 2 29) rfl rfl
    simpa [SubexponentialSAT.BitProgram.execInstr, cfg, r', SubexponentialSAT.BitProgram.readRegs] using h
  have h₃ : SubexponentialSAT.BitProgram.step program (cfg (some 2) r' xs ys acc [] [] []) =
      some (cfg (some (if b then 3 else 27)) r' xs ys acc [] [] []) := by
    have h := SubexponentialSAT.BitProgram.step_code program (cfg (some 2) r' xs ys acc [] [] [])
      2 (.branch 1 3 27) rfl rfl
    cases b <;>
      simpa [SubexponentialSAT.BitProgram.execInstr, cfg, r', SubexponentialSAT.BitProgram.readRegs] using h
  exact .cons h₁ (.cons h₂ (.cons h₃ (.refl _)))

theorem reset_carry (r : Regs) (xs ys acc : List Bool) :
    SubexponentialSAT.BitProgram.Trace program 1 (cfg (some 10) r xs ys acc ys [] [])
      (cfg (some 11) (Function.update r 0 false) xs ys acc ys [] []) := by
  apply Trace.of_iterate
  simp [ SubexponentialSAT.BitProgram.step, SubexponentialSAT.BitProgram.execInstr,
    program, cfg]

theorem shift (r : Regs) (xs ys acc : List Bool) :
    SubexponentialSAT.BitProgram.Trace program 2 (cfg (some 27) r xs ys acc [] [] [])
      (loopCfg (Function.update r 1 false) xs (false :: ys) acc) := by
  apply Trace.of_iterate
  simp [Function.iterate_succ_apply, SubexponentialSAT.BitProgram.step, SubexponentialSAT.BitProgram.execInstr,
    program, cfg, loopCfg]

/-- One full multiplier iteration, including all copy and arithmetic work. -/
theorem round (r : Regs) (b : Bool) (xs ys acc : List Bool) :
    ∃ rf : Regs, SubexponentialSAT.BitProgram.RunsIn program
      (30 * (max acc.length ys.length + 1))
      (loopCfg r (b :: xs) ys acc)
      (loopCfg rf xs (false :: ys) (if b then add acc ys else acc)) := by
  cases b with
  | false =>
      let r' := SubexponentialSAT.BitProgram.readRegs r 1 3 (some false)
      have ht := (enter_round r false xs ys acc).trans (shift r' xs ys acc)
      refine ⟨Function.update r' 1 false, 5, by omega, ?_⟩
      exact ht
  | true =>
      let r₁ := SubexponentialSAT.BitProgram.readRegs r 1 3 (some true)
      let r₂ := SubexponentialSAT.BitProgram.readRegs r₁ 1 3 none
      let r₃ := Function.update r₂ 0 false
      have hp := (enter_round r true xs ys acc).trans (copy_block r₁ xs ys acc)
      have hp' := hp.trans (reset_carry r₂ xs ys acc)
      obtain ⟨r₄, ha⟩ := add_block r₃ xs ys acc ys [] []
      have ha' : SubexponentialSAT.BitProgram.RunsIn program (10 * (max acc.length ys.length + 1))
          (cfg (some 11) r₃ xs ys acc ys [] [])
          (cfg (some 24) r₄ xs ys [] [] [] (add acc ys).reverse) := by
        simpa [r₃, add] using ha
      let r₅ := SubexponentialSAT.BitProgram.readRegs r₄ 1 3 none
      have hq := (transfer_block r₄ xs ys (add acc ys)).trans (shift r₅ xs ys (add acc ys))
      have hpRun : SubexponentialSAT.BitProgram.RunsIn program (3 + (7 * ys.length + 4) + 1)
          (loopCfg r (true :: xs) ys acc)
          (cfg (some 11) r₃ xs ys acc ys [] []) :=
        ⟨_, le_rfl, hp'⟩
      have hqRun : SubexponentialSAT.BitProgram.RunsIn program (3 * (add acc ys).length + 2 + 2)
          (cfg (some 24) r₄ xs ys [] [] [] (add acc ys).reverse)
          (loopCfg (Function.update r₅ 1 false) xs (false :: ys) (add acc ys)) :=
        ⟨_, le_rfl, hq⟩
      refine ⟨Function.update r₅ 1 false, ?_⟩
      have ht := (hpRun.trans ha').trans hqRun
      have hlen := length_add acc ys
      exact ht.mono (by omega)

theorem finish (r : Regs) (ys acc : List Bool) :
    ∃ rf : Regs, SubexponentialSAT.BitProgram.Trace program (2 * ys.length + 5)
      (loopCfg r [] ys acc) (cfg none rf [] [] acc [] [] []) := by
  let r₁ := SubexponentialSAT.BitProgram.readRegs r 1 3 none
  have hp : SubexponentialSAT.BitProgram.Trace program 2 (loopCfg r [] ys acc)
      (cfg (some 29) r₁ [] ys acc [] [] []) := by
    apply Trace.of_iterate
    simp [Function.iterate_succ_apply, SubexponentialSAT.BitProgram.step, SubexponentialSAT.BitProgram.execInstr,
      program, cfg, loopCfg, r₁, SubexponentialSAT.BitProgram.readRegs]
  have hc := SubexponentialSAT.StackRoutines.clear_trace program 1 1 3 29 30 31 rfl rfl
    r₁ (stackState [] ys acc [] [] [])
  have hc' : SubexponentialSAT.BitProgram.Trace program (2 * ys.length + 2)
      (cfg (some 29) r₁ [] ys acc [] [] [])
      (cfg (some 31) (SubexponentialSAT.BitProgram.readRegs r₁ 1 3 none) [] [] acc [] [] []) := by
    simpa [SubexponentialSAT.StackRoutines.clearResult, SubexponentialSAT.StackRoutines.clearStacks, cfg] using hc
  have hh := SubexponentialSAT.StackRoutines.halt_after_trace program (hp.trans hc') 31 rfl rfl
  refine ⟨SubexponentialSAT.BitProgram.readRegs r₁ 1 3 none, ?_⟩
  convert hh using 1 <;> simp [cfg] ; omega

/-- The complete fixed program computes the accumulator specification.  The
bound counts every executed Boolean instruction and every stack operation. -/
theorem run (r : Regs) (xs ys acc : List Bool) (B : ℕ)
    (hys : ys.length ≤ B) (hacc : acc.length ≤ B) :
    ∃ rf : Regs, SubexponentialSAT.BitProgram.RunsIn program
      (30 * (xs.length + 1) * (B + xs.length + 1))
      (loopCfg r xs ys acc) (cfg none rf [] [] (accumulate xs ys acc) [] [] []) := by
  induction xs generalizing r ys acc B with
  | nil =>
      obtain ⟨rf, hf⟩ := finish r ys acc
      exact ⟨rf, 2 * ys.length + 5, by simp; omega, hf⟩
  | cons b xs ih =>
      obtain ⟨r', hr⟩ := round r b xs ys acc
      have hnext : (if b then add acc ys else acc).length ≤ B + 1 := by
        have ha := length_add acc ys
        cases b <;> simp <;> omega
      obtain ⟨rf, hf⟩ := ih r' (false :: ys) (if b then add acc ys else acc) (B + 1)
        (by simpa using Nat.succ_le_succ hys) hnext
      refine ⟨rf, ?_⟩
      have ht := hr.trans hf
      have hb : max acc.length ys.length ≤ B := max_le hacc hys
      have hcost : 30 * (max acc.length ys.length + 1) +
          30 * (xs.length + 1) * (B + 1 + xs.length + 1) ≤
          30 * ((b :: xs).length + 1) * (B + (b :: xs).length + 1) := by
        simp only [List.length_cons]
        nlinarith
      exact ht.mono hcost

theorem run_value (xs ys : List Bool) :
    ∃ rf : Regs, ∃ output : List Bool,
      BinaryArithmetic.toNat output = BinaryArithmetic.toNat xs * BinaryArithmetic.toNat ys ∧
      SubexponentialSAT.BitProgram.RunsIn program (30 * (xs.length + 1) * (ys.length + xs.length + 1))
        (loopCfg (fun _ => false) xs ys [])
        (cfg none rf [] [] output [] [] []) := by
  obtain ⟨rf, hr⟩ := run (fun _ => false) xs ys [] ys.length le_rfl (by simp)
  refine ⟨rf, accumulate xs ys [], ?_, hr⟩
  simpa using accumulate_value xs ys []

/-- The fixed-control multiplier also runs on the actual primitive tape
machine. Its polynomial bound contains no word-sized arithmetic operation. -/
theorem primitive_value (xs ys : List Bool) :
    ∃ rf : Regs, ∃ output : List Bool,
      BinaryArithmetic.toNat output = BinaryArithmetic.toNat xs * BinaryArithmetic.toNat ys ∧
      SubexponentialSAT.Computation.RunsIn (SubexponentialSAT.BitProgram.primitive program).step
        (SubexponentialSAT.BitProgram.primitiveOverhead program *
          (30 * (xs.length + 1) * (ys.length + xs.length + 1)))
        (SubexponentialSAT.BitProgram.primitiveCfg program (loopCfg (fun _ => false) xs ys []))
        (SubexponentialSAT.BitProgram.primitiveCfg program (cfg none rf [] [] output [] [] [])) := by
  obtain ⟨rf, output, hv, hr⟩ := run_value xs ys
  exact ⟨rf, output, hv, SubexponentialSAT.BitProgram.primitive_execution program hr⟩

end Mul

end SubexponentialSAT.BinaryPrograms

end OAI.Algorithms
