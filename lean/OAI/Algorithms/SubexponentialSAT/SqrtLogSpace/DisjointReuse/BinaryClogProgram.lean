import OAI.Algorithms.SubexponentialSAT.CounterPrograms
import OAI.Algorithms.SubexponentialSAT.BinaryArithmetic
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.StackRoutines
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms
import Mathlib.Data.List.Induction

/-! Actual floor and ceiling logarithm bit programs, without packing or schedule imports. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Floor

open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.CounterPrograms

theorem value_eq_toNat (xs : List Bool) : value xs = BinaryArithmetic.toNat xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [value, BinaryArithmetic.toNat,
      BinaryArithmetic.bitVal, ih]

theorem value_append (xs ys : List Bool) :
    value (xs ++ ys) = value xs + 2 ^ xs.length * value ys := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
      simp only [List.cons_append, value, List.length_cons, ih, pow_succ]
      ring

theorem value_lt_two_pow_length (xs : List Bool) : value xs < 2 ^ xs.length := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
      cases b <;> simp only [value, Bool.toNat_false, Bool.toNat_true,
        List.length_cons, pow_succ] <;> omega

/-- Consume leading zeroes and the first one of a most-significant-first word. -/
def trimTail : List Bool → List Bool
  | [] => []
  | false :: xs => trimTail xs
  | true :: xs => xs

theorem trimTail_length_le (xs : List Bool) : (trimTail xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [trimTail]
  | cons b xs ih => cases b <;> simp [trimTail]; omega

/-- A most-significant one followed by `m` bits has binary logarithm `m`. -/
theorem log2_value_append_true (xs : List Bool) :
    Nat.log2 (value (xs ++ [true])) = xs.length := by
  have hbound := value_lt_two_pow_length xs
  have hpow : 0 < 2 ^ xs.length := Nat.two_pow_pos _
  have hval : value (xs ++ [true]) = value xs + 2 ^ xs.length := by
    simp [value_append, value]
  have hpos : value (xs ++ [true]) ≠ 0 := by omega
  apply Nat.le_antisymm
  · have hlt : value (xs ++ [true]) < 2 ^ (xs.length + 1) := by
      rw [pow_succ]
      omega
    have h := (Nat.log2_lt hpos).mpr hlt
    omega
  · exact (Nat.le_log2 hpos).mpr (by omega)

theorem trimTail_reverse_length (xs : List Bool) :
    (trimTail xs.reverse).length = Nat.log2 (value xs) := by
  induction xs using List.reverseRecOn with
  | nil => simp [trimTail, value]
  | append_singleton xs b ih =>
      cases b with
      | false => simpa [List.reverse_append, trimTail, value_append, value] using ih
      | true => simp [List.reverse_append, trimTail, log2_value_append_true]

def atoms {r s : ℕ} : List (StructuredProgram.Atom r s) → StructuredProgram.Cmd r s
  | [] => .skip
  | op :: ops => .seq (.atom op) (atoms ops)

def runAtoms {r s : ℕ} : List (StructuredProgram.Atom r s) →
    StructuredProgram.State r s → StructuredProgram.State r s
  | [], d => d
  | op :: ops, d => runAtoms ops (op.eval d)

theorem atoms_eval {r s : ℕ} (ops : List (StructuredProgram.Atom r s))
    (d : StructuredProgram.State r s) :
    StructuredProgram.Eval (atoms ops) ops.length d (runAtoms ops d) := by
  induction ops generalizing d with
  | nil => exact .skip d
  | cons op ops ih =>
      simpa only [atoms, runAtoms, List.length_cons, Nat.add_comm 1] using
        StructuredProgram.Eval.seq (.atom op d) (ih (op.eval d))

/-- Four low bits are discarded; the two read registers are then cleared. -/
def trimProgram : Program 3 3 6 where
  inputStack := 1
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .pop 1 0 1 1
    | 1 => .branch 1 2 3
    | 2 => .branch 0 3 0
    | 3 => .set 0 false 4
    | 4 => .set 1 false 5
    | _ => .halt

def trimCfg (pc : Option (Fin 6)) (b present : Bool) (xs : List Bool) : Cfg 3 3 6 :=
  ⟨pc, counterRegs b present false, lengthStacks [] xs []⟩

@[simp] theorem update_lengthStacks_one (a b c d : List Bool) :
    Function.update (lengthStacks a b c) 1 d = lengthStacks a d c := by
  funext i
  fin_cases i <;> simp [lengthStacks]

theorem trim_finish (b present : Bool) (xs : List Bool) :
    Trace trimProgram 3 (trimCfg (some 3) b present xs) (trimCfg none false false xs) := by
  refine .cons (b := trimCfg (some 4) false present xs) ?_
    (.cons (b := trimCfg (some 5) false false xs) ?_ (.cons ?_ (.refl _)))
  all_goals simp [step, trimProgram, trimCfg, execInstr]

def trimCost : List Bool → ℕ
  | [] => 5
  | false :: xs => trimCost xs + 3
  | true :: _ => 6

theorem trim_trace (xs : List Bool) (b present : Bool) :
    Trace trimProgram (trimCost xs) (trimCfg (some 0) b present xs)
      (trimCfg none false false (trimTail xs)) := by
  induction xs generalizing b present with
  | nil =>
      refine .cons (b := trimCfg (some 1) false false []) ?_
        (.cons ?_ (trim_finish false false []))
      all_goals simp [step, trimProgram, trimCfg, execInstr, readRegs]
  | cons a xs ih =>
      cases a with
      | false =>
          refine .cons (b := trimCfg (some 1) false true xs) ?_
            (.cons (b := trimCfg (some 2) false true xs) ?_
              (.cons ?_ (ih false true)))
          all_goals simp [step, trimProgram, trimCfg, execInstr, readRegs]
      | true =>
          refine .cons (b := trimCfg (some 1) true true xs) ?_
            (.cons (b := trimCfg (some 2) true true xs) ?_
              (.cons ?_ (trim_finish true true xs)))
          all_goals simp [step, trimProgram, trimCfg, execInstr, readRegs]

theorem trimCost_le (xs : List Bool) : trimCost xs ≤ 3 * xs.length + 6 := by
  induction xs with
  | nil => simp [trimCost]
  | cons a xs ih => cases a <;> simp only [trimCost, List.length_cons] <;> omega

theorem trim_complete_trace (xs : List Bool) :
    Trace trimProgram (trimCost xs) (initial trimProgram xs)
      (terminal trimProgram (trimTail xs)) := by
  have hi : initial trimProgram xs = trimCfg (some 0) false false xs := by
    simp [initial, trimProgram, trimCfg]
    constructor <;> funext i <;> fin_cases i <;> simp [counterRegs, lengthStacks]
  have ht : terminal trimProgram (trimTail xs) = trimCfg none false false (trimTail xs) := by
    simp [terminal, trimProgram, trimCfg]
    constructor <;> funext i <;> fin_cases i <;> simp [counterRegs, lengthStacks]
  rw [hi, ht]
  exact trim_trace xs false false

theorem trim_complete_runs (xs : List Bool) :
    RunsIn trimProgram (3 * xs.length + 6) (initial trimProgram xs)
      (terminal trimProgram (trimTail xs)) :=
  ⟨trimCost xs, trimCost_le xs, trim_complete_trace xs⟩

/-! ## Concrete input reversal -/

def reverseTransfer : Program 3 3 4 := StackRoutines.transferProgram 0 1 0 1

theorem reverseTransfer_trace (xs : List Bool) :
    Trace reverseTransfer (3 * xs.length + 3) (initial reverseTransfer xs)
      (terminal reverseTransfer xs.reverse) := by
  have h := StackRoutines.transferProgram_trace (r := 3) (s := 3)
    0 1 0 1 (by decide) (by decide) (fun _ => false)
    (fun i => if i = 0 then xs else [])
  have ht : StackRoutines.transferResult (3 : Fin 4) (0 : Fin 3) 1 (0 : Fin 3) 1
      (fun _ => false) (fun i => if i = 0 then xs else []) =
      {terminal reverseTransfer xs.reverse with pc := some 3} := by
    simp [StackRoutines.transferResult, StackRoutines.transferStacks,
      reverseTransfer, StackRoutines.transferProgram, readRegs]
    funext i
    fin_cases i <;> simp
  have hh : Trace reverseTransfer 1
      {terminal reverseTransfer xs.reverse with pc := some 3}
      (terminal reverseTransfer xs.reverse) := by
    refine .cons ?_ (.refl _)
    simp [step, reverseTransfer, StackRoutines.transferProgram, execInstr, terminal]
  rw [ht] at h
  change Trace reverseTransfer (3 * xs.length + 2) (initial reverseTransfer xs)
    {terminal reverseTransfer xs.reverse with pc := some 3} at h
  exact h.trans hh

theorem enter_terminal_eq_initial {r s l m : ℕ}
    (p : Program r s l) (q : Program r s m) (h : p.outputStack = q.inputStack)
    (word : List Bool) :
    ProgramLinking.enter q (terminal p word) = initial q word := by
  simp [ProgramLinking.enter, initial, h]

theorem link_io_runs {r s l m n₁ n₂ : ℕ}
    (p : Program r s l) (q : Program r s m) (h : p.outputStack = q.inputStack)
    (input middle output : List Bool)
    (hp : RunsIn p n₁ (initial p input) (terminal p middle))
    (hq : RunsIn q n₂ (initial q middle) (terminal q output)) :
    RunsIn (ProgramLinking.link p q) (n₁ + n₂)
      (initial (ProgramLinking.link p q) input)
      (terminal (ProgramLinking.link p q) output) := by
  exact ProgramLinking.link_complete_runsIn p q input output hp rfl
    (by simpa only [enter_terminal_eq_initial p q h middle] using hq)

def prepareLogProgram : Program 3 3 10 := ProgramLinking.link reverseTransfer trimProgram

theorem prepareLog_runs (xs : List Bool) :
    RunsIn prepareLogProgram (6 * xs.length + 9)
      (initial prepareLogProgram xs)
      (terminal prepareLogProgram (trimTail xs.reverse)) := by
  have h := link_io_runs reverseTransfer trimProgram rfl xs xs.reverse
    (trimTail xs.reverse) ⟨_, le_rfl, reverseTransfer_trace xs⟩
    (trim_complete_runs xs.reverse)
  change RunsIn (ProgramLinking.link reverseTransfer trimProgram) (6 * xs.length + 9)
    (initial (ProgramLinking.link reverseTransfer trimProgram) xs)
    (terminal (ProgramLinking.link reverseTransfer trimProgram) (trimTail xs.reverse))
  convert h using 1
  rw [List.length_reverse]
  omega

/-! ## Reindex and call the checked binary word-length counter -/

theorem extend_equiv {α β γ : Type*} (e : α ≃ β) (f : α → γ) (frame : β → γ) :
    Function.extend e f frame = fun b => f (e.symm b) := by
  funext b
  simp

theorem lift_equiv_initial {r s l : ℕ} (p : Program r s l) (e : Fin s ≃ Fin s)
    (frame : Cfg r s l) (word : List Bool) :
    ProgramLinking.embedCfg id e id none frame (initial p word) =
      initial (ProgramLinking.liftProgram p id e) word := by
  simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc, initial,
    extend_equiv]
  funext b
  simp only [e.symm_apply_eq]

theorem lift_equiv_terminal {r s l : ℕ} (p : Program r s l) (e : Fin s ≃ Fin s)
    (frame : Cfg r s l) (word : List Bool) :
    ProgramLinking.embedCfg id e id none frame (terminal p word) =
      terminal (ProgramLinking.liftProgram p id e) word := by
  simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc, terminal,
    extend_equiv]
  funext b
  simp only [e.symm_apply_eq]

def swapStacks : Equiv.Perm (Fin 3) := Equiv.swap 0 1

def swappedLengthProgram : Program 3 3 14 :=
  ProgramLinking.liftProgram lengthProgram id swapStacks

theorem swappedLength_correct (xs : List Bool) :
    ∃ output, value output = xs.length ∧ output.length ≤ xs.length ∧
      RunsIn swappedLengthProgram (xs.length * (8 * xs.length + 10) + 3)
        (initial swappedLengthProgram xs) (terminal swappedLengthProgram output) := by
  obtain ⟨output, hvalue, hlen, hrun⟩ := length_correct xs
  have h := ProgramLinking.liftProgram_runsIn lengthProgram id swapStacks
    (initial swappedLengthProgram []) Function.injective_id swapStacks.injective hrun
  refine ⟨output, hvalue, hlen, ?_⟩
  simpa only [swappedLengthProgram, lift_equiv_initial, lift_equiv_terminal] using h

def logProgram : Program 3 3 24 := ProgramLinking.link prepareLogProgram swappedLengthProgram

def logBound (L : ℕ) : ℕ := L * (8 * L + 16) + 12

theorem logBound_eq (L : ℕ) : logBound L = 8 * L ^ 2 + 16 * L + 12 := by
  unfold logBound
  ring

theorem logBound_mono {L M : ℕ} (h : L ≤ M) : logBound L ≤ logBound M := by
  exact Nat.add_le_add_right (Nat.mul_le_mul h (by omega : 8 * L + 16 ≤ 8 * M + 16)) 12

/-- Actual fixed-table logarithm program, correct for arbitrary padded words. -/
theorem log_correct (xs : List Bool) :
    ∃ output, value output = Nat.log2 (value xs) ∧ output.length ≤ xs.length ∧
      RunsIn logProgram (logBound xs.length)
        (initial logProgram xs) (terminal logProgram output) := by
  obtain ⟨output, hvalue, hlen, hcount⟩ := swappedLength_correct (trimTail xs.reverse)
  have hrun := link_io_runs prepareLogProgram swappedLengthProgram rfl
    xs (trimTail xs.reverse) output (prepareLog_runs xs) hcount
  have htail : (trimTail xs.reverse).length ≤ xs.length := by
    simpa using trimTail_length_le xs.reverse
  refine ⟨output, hvalue.trans (trimTail_reverse_length xs), hlen.trans htail, hrun.mono ?_⟩
  have hmul := Nat.mul_le_mul htail
    (show 8 * (trimTail xs.reverse).length + 10 ≤ 8 * xs.length + 10 by omega)
  dsimp [logBound]
  nlinarith

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Floor

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Setup

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

abbrev Data := StructuredProgram.State 3 3
abbrev io (xs : List Bool) : Data := StructuredProgram.ioState 0 xs

def incrementPorts : Fin 2 → Fin 3 := ![0, 1]

theorem incrementPorts_injective : Function.Injective incrementPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [incrementPorts]

def increment : Cmd 3 3 :=
  .call (ProgramLinking.liftProgram (CounterPrograms.rippleProgram true) id incrementPorts)

theorem increment_eval (xs : List Bool) :
    Eval increment (CounterPrograms.rippleCost true xs + 1) (io xs) (io (ripple true xs)) := by
  have he := eval_call_lifted (CounterPrograms.rippleProgram true) id incrementPorts
    (io xs) Function.injective_id incrementPorts_injective
    (a := StructuredProgram.ioState (0 : Fin 2) xs)
    (b := StructuredProgram.ioState (0 : Fin 2) (ripple true xs))
    (CounterPrograms.ripple_terminal_trace true xs)
  have ha : embedState id incrementPorts (io xs)
      (StructuredProgram.ioState (0 : Fin 2) xs) = io xs := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id incrementPorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
  have hb : embedState id incrementPorts (io xs)
      (StructuredProgram.ioState (0 : Fin 2) (ripple true xs)) = io (ripple true xs) := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id incrementPorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> simp_all [incrementPorts, io, StructuredProgram.ioState,
        Fin.exists_fin_succ]
  change Eval increment _ (embedState id incrementPorts (io xs)
    (StructuredProgram.ioState (0 : Fin 2) xs))
    (embedState id incrementPorts (io xs)
      (StructuredProgram.ioState (0 : Fin 2) (ripple true xs))) at he
  simpa only [increment, ha, hb] using he

def logarithm : Cmd 3 3 := .call Floor.logProgram

theorem logarithm_eval (xs : List Bool) :
    ∃ output t, value output = Nat.log2 (value xs) ∧ output.length ≤ xs.length ∧
      t ≤ Floor.logBound xs.length ∧
      Eval logarithm t (io xs) (io output) := by
  obtain ⟨output, hv, hl, t, ht, he⟩ := Floor.log_correct xs
  exact ⟨output, t, hv, hl, ht, .call _ he⟩

/-- The floor binary logarithm plus one, with zero mapped to one. -/
def logSucc : Cmd 3 3 := .seq logarithm increment

theorem logSucc_eval (xs : List Bool) :
    ∃ output t, value output = Nat.log2 (value xs) + 1 ∧ output.length ≤ xs.length + 1 ∧
      t ≤ 32 * (xs.length + 1)^2 ∧ Eval logSucc t (io xs) (io output) := by
  obtain ⟨ys, t, hv, hl, ht, he⟩ := logarithm_eval xs
  refine ⟨ripple true ys, t + (CounterPrograms.rippleCost true ys + 1), ?_, ?_, ?_,
    he.seq (increment_eval ys)⟩
  · rw [CounterPrograms.value_increment, hv]
  · exact (CounterPrograms.ripple_length_le true ys).trans (by omega)
  · have hc := CounterPrograms.rippleCost_le true ys
    rw [Floor.logBound_eq] at ht
    nlinarith


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Setup

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

abbrev Data := StructuredProgram.State 3 3
abbrev io := Setup.io

def decrement : Cmd 3 3 :=
  .call (ProgramLinking.liftProgram (CounterPrograms.rippleProgram false)
    id Setup.incrementPorts)

theorem decrement_eval (xs : List Bool) :
    Eval decrement (CounterPrograms.rippleCost false xs + 1)
      (io xs) (io (ripple false xs)) := by
  have he := eval_call_lifted (CounterPrograms.rippleProgram false) id
    Setup.incrementPorts (io xs) Function.injective_id Setup.incrementPorts_injective
    (a := StructuredProgram.ioState (0 : Fin 2) xs)
    (b := StructuredProgram.ioState (0 : Fin 2) (ripple false xs))
    (CounterPrograms.ripple_terminal_trace false xs)
  have ha : embedState id Setup.incrementPorts (io xs)
      (StructuredProgram.ioState (0 : Fin 2) xs) = io xs := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id Setup.incrementPorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
  have hb : embedState id Setup.incrementPorts (io xs)
      (StructuredProgram.ioState (0 : Fin 2) (ripple false xs)) = io (ripple false xs) := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id Setup.incrementPorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> simp_all [Setup.incrementPorts, io, Setup.io,
        StructuredProgram.ioState, Fin.exists_fin_succ]
  simpa only [decrement, ha, hb] using he

def zeroPorts : CounterForPrograms.Ports 3 3 where
  register := Function.Embedding.refl _
  counter := 0
  scratch := 1
  counter_ne_scratch := by decide

def reset : Cmd 3 3 := .base (Floor.atoms
  [.set 0 false, .set 1 false, .set 2 false])

theorem reset_eval (d : Data) : Eval reset 3 d ⟨fun _ => false, d.stacks⟩ := by
  have h := Floor.atoms_eval
    ([.set 0 false, .set 1 false, .set 2 false] : List (StructuredProgram.Atom 3 3)) d
  convert Eval.base h using 1
  · rfl
  · apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · rfl

def command : Cmd 3 3 := .seq decrement
  (.seq (CounterForPrograms.zeroCmd zeroPorts)
    (.ite 2 reset (.seq reset Setup.logSucc)))

theorem clog_eq_log_pred (t : ℕ) (ht : 2 ≤ t) :
    Nat.clog 2 t = Nat.log2 (t-1) + 1 := by
  rw [Nat.log2_eq_log_two]
  apply Nat.le_antisymm
  · apply (Nat.le_pow_iff_clog_le (by decide : 1 < 2)).mp
    have hp := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (t-1)
    omega
  · have hp := Nat.pow_log_le_self 2 (show t-1 ≠ 0 by omega)
    have hlt : 2 ^ Nat.log 2 (t-1) < t := by omega
    have hh := (Nat.pow_lt_iff_lt_clog (by decide : 1 < 2)).mp hlt
    omega

private theorem zero_branch_cost_le (r L : ℕ) (hr : r ≤ 8 * L + 7) :
    (r + 1) + ((8 * L + 6) + (3 + 1)) ≤ 64 * (L + 2) ^ 2 := by
  nlinarith

private theorem nonzero_branch_cost_le (r t L : ℕ) (hr : r ≤ 8 * L + 7)
    (ht : t ≤ 32 * (L + 1) ^ 2) :
    (r + 1) + ((8 * L + 6) + ((3 + t) + 1)) ≤ 64 * (L + 2) ^ 2 := by
  nlinarith

theorem command_eval (xs : List Bool) (hx : 0 < value xs) :
    ∃ output n, value output = Nat.clog 2 (value xs) ∧
      output.length ≤ xs.length + 1 ∧ n ≤ 64*(xs.length+2)^2 ∧
      Eval command n (io xs) (io output) := by
  let ys := ripple false xs
  let z := CounterForPrograms.zeroResult zeroPorts (io ys)
  have hy : value ys = value xs - 1 := by
    have h := CounterPrograms.value_decrement hx
    dsimp [ys]
    omega
  have hlen : ys.length = xs.length := CounterPrograms.decrement_length hx
  have hz := CounterForPrograms.zero_eval zeroPorts (io ys) (by rfl)
  have hzs : z.stacks = (io ys).stacks := by
    exact CounterForPrograms.install_stacks_self zeroPorts (io ys) _ _ _ rfl
  have hzf : z.regs 2 = CounterPrograms.isZero ys := by
    exact CounterForPrograms.install_register zeroPorts (io ys) _ _ _ _ _ 2
  have hr : Eval reset 3 z (io ys) := by
    simpa only [hzs] using reset_eval z
  have hc := CounterPrograms.rippleCost_le false xs
  by_cases hzero : value ys = 0
  · have ht : value xs = 1 := by omega
    have hb : z.regs 2 = true := hzf.trans ((CounterPrograms.isZero_eq_true_iff ys).mpr hzero)
    refine ⟨ys, (CounterPrograms.rippleCost false xs+1)+((8*ys.length+6)+(3+1)), ?_, ?_, ?_, ?_⟩
    · simp [hzero, ht]
    · omega
    · rw [hlen]
      exact zero_branch_cost_le _ _ hc
    · exact (decrement_eval xs).seq (hz.seq (Eval.ite_true hb hr))
  · obtain ⟨out,n,hv,hl,hn,he⟩ := Setup.logSucc_eval ys
    have hb : z.regs 2 = false := hzf.trans
      ((CounterPrograms.isZero_eq_false_iff ys).mpr (by omega))
    refine ⟨out,(CounterPrograms.rippleCost false xs+1)+((8*ys.length+6)+((3+n)+1)), ?_, ?_, ?_, ?_⟩
    · rw [hv, hy, clog_eq_log_pred _ (by omega)]
    · omega
    · rw [hlen] at hn ⊢
      exact nonzero_branch_cost_le _ _ _ hc hn
    · exact (decrement_eval xs).seq (hz.seq (Eval.ite_false hb (hr.seq he)))

def program := compiled command 0 0

theorem program_runs (xs : List Bool) (hx : 0 < value xs) :
    ∃ output, value output = Nat.clog 2 (value xs) ∧
      output.length ≤ xs.length+1 ∧
      RunsIn program (65*(xs.length+2)^2)
        (initial program xs) (terminal program output) := by
  obtain ⟨out,n,hv,hl,hn,he⟩ := command_eval xs hx
  exact ⟨out,hv,hl,n+1,by nlinarith,compiled_io_trace 0 0 he⟩


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram
