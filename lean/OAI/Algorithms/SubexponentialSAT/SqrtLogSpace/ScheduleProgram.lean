import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Asymptotics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParameterArithmetic
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace

/-! Actual binary construction of the disjoint-sparsification parameter.
All arithmetic uses fixed finite programs; the input numeral is runtime stack data. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ScheduleProgram

open BitProgram StructuredCalls
open BinaryArithmetic (toNat)

abbrev Data := State 8 32

def resetRegs (r : Fin 8 → Bool) : Fin 8 → Bool :=
  Function.update (Function.update (Function.update r 0 false) 1 false) 2 false

def reset : Cmd 8 32 := .base
  (.seq (.atom (.set 0 false)) (.seq (.atom (.set 1 false)) (.atom (.set 2 false))))

theorem reset_eval (d : Data) : Eval reset 3 d ⟨resetRegs d.regs, d.stacks⟩ := by
  exact .base (.seq (.atom _ _) (.seq (.atom _ _) (.atom _ _)))

def clogStacks (port : Fin 32) : Fin 3 → Fin 32 := ![port, 6, 7]

theorem clogStacks_injective (port : Fin 32) (h6 : port ≠ 6) (h7 : port ≠ 7) :
    Function.Injective (clogStacks port) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [clogStacks]

def clogAt (port : Fin 32) : Cmd 8 32 :=
  .seq reset (.call (ProgramLinking.liftProgram DisjointReuse.BinaryClogProgram.program
    (Fin.castAdd 5) (clogStacks port)))

/-- The two work stacks are restored, and all other caller stacks are framed. -/
theorem clogAt_eval (port : Fin 32) (h6 : port ≠ 6) (h7 : port ≠ 7)
    (d : Data) (hwork6 : d.stacks 6 = []) (hwork7 : d.stacks 7 = [])
    (hpos : 0 < toNat (d.stacks port)) :
    ∃ t word,
      Eval (clogAt port) t d ⟨resetRegs d.regs, Function.update d.stacks port word⟩ ∧
      toNat word = Nat.clog 2 (toNat (d.stacks port)) ∧
      word.length ≤ (d.stacks port).length + 1 ∧
      t ≤ 68 * ((d.stacks port).length + 2) ^ 2 := by
  obtain ⟨word, hv, hl, t, ht, htrace⟩ :=
    DisjointReuse.BinaryClogProgram.program_runs (d.stacks port)
      (by simpa only [CounterPrograms.value_eq_toNat] using hpos)
  let a : Data := ⟨resetRegs d.regs, d.stacks⟩
  have he (xs : List Bool) :
      embedState (Fin.castAdd 5) (clogStacks port) a (StructuredProgram.ioState 0 xs) =
        (⟨resetRegs d.regs, Function.update d.stacks port xs⟩ : Data) := by
    apply embedState_eq_of_ports _ _ _ _ _ (Fin.castAdd_injective 3 5)
      (clogStacks_injective port h6 h7)
    · intro i
      fin_cases i <;> simp [resetRegs]
    · intro i hi
      rfl
    · intro i
      fin_cases i <;> simp [clogStacks, h6.symm, h7.symm,
        hwork6, hwork7]
    · intro i hi
      have hn : i ≠ port := fun h => hi ⟨0, h.symm⟩
      simp [a, hn]
  have hc := eval_call_lifted DisjointReuse.BinaryClogProgram.program
    (Fin.castAdd 5) (clogStacks port) a (Fin.castAdd_injective 3 5)
    (clogStacks_injective port h6 h7)
    (a := StructuredProgram.ioState 0 (d.stacks port))
    (b := StructuredProgram.ioState 0 word) htrace
  change Eval _ t
    (embedState (Fin.castAdd 5) (clogStacks port) a
      (StructuredProgram.ioState 0 (d.stacks port)))
    (embedState (Fin.castAdd 5) (clogStacks port) a
      (StructuredProgram.ioState 0 word)) at hc
  rw [he, he, Function.update_eq_self] at hc
  refine ⟨3 + t, word, (reset_eval d).seq hc, ?_, hl, ?_⟩
  · simpa only [CounterPrograms.value_eq_toNat] using hv
  · have hp : 1 ≤ ((d.stacks port).length + 2) ^ 2 := by
      simpa using Nat.pow_le_pow_left (show 1 ≤ (d.stacks port).length + 2 by omega) 2
    omega

def work5 : Fin 5 ↪ Fin 32 := (Fin.natAddEmb 6).trans (Fin.castAddEmb 21)
def work6 : Fin 6 ↪ Fin 32 := (Fin.natAddEmb 6).trans (Fin.castAddEmb 20)
def work13 : Fin 13 ↪ Fin 32 := (Fin.natAddEmb 6).trans (Fin.castAddEmb 13)

def squarePorts : ArithmeticCalls.Ports 32 where
  left := 2
  right := 2
  out := 3
  work := work5
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left i := by
    intro h
    have hv := congrArg Fin.val h
    change 6 + i.val = _ at hv
    omega
  work_ne_right i := by
    intro h
    have hv := congrArg Fin.val h
    change 6 + i.val = _ at hv
    omega
  work_ne_out i := by
    intro h
    have hv := congrArg Fin.val h
    change 6 + i.val = _ at hv
    omega

def sqrtPorts : SqrtLog.LeafParameterArithmetic.SqrtPorts 32 where
  input := 1
  out := 4
  work := work13
  out_ne_input := by decide
  work_ne_input i := by
    intro h
    have hv := congrArg Fin.val h
    change 6 + i.val = _ at hv
    omega
  work_ne_out i := by
    intro h
    have hv := congrArg Fin.val h
    change 6 + i.val = _ at hv
    omega

def quotientPorts : SqrtLog.LeafParameterArithmetic.QuotientPorts 32 where
  left := 4
  right := 3
  out := 5
  work := work6
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left i := by
    intro h
    have hv := congrArg Fin.val h
    change 6 + i.val = _ at hv
    omega
  work_ne_right i := by
    intro h
    have hv := congrArg Fin.val h
    change 6 + i.val = _ at hv
    omega
  work_ne_out i := by
    intro h
    have hv := congrArg Fin.val h
    change 6 + i.val = _ at hv
    omega

/-- Ports0..5 retain n, lambda, nu, nu squared, sqrt lambda, and s.
Scratch6..18 is reused and restored by each actual subroutine. -/
def command : Cmd 8 32 :=
  .seq (ArithmeticCalls.copyAt 0 1 6)
    (.seq (clogAt 1)
      (.seq (ArithmeticCalls.copyAt 1 2 6)
        (.seq (clogAt 2)
          (.seq (ArithmeticCalls.multiplyAt squarePorts)
            (.seq (SqrtLog.LeafParameterArithmetic.sqrtAt sqrtPorts)
              (SqrtLog.LeafParameterArithmetic.quotientAt quotientPorts))))))

/-- Six persistent local words; every local work stack is empty at boundaries. -/
def slots (words : Fin 6 → List Bool) : Fin 32 → List Bool :=
  fun i => if h : i.val < 6 then words ⟨i.val, h⟩ else []

@[simp] theorem slots_low (words : Fin 6 → List Bool) (i : Fin 6) :
    slots words (Fin.castAdd 26 i) = words i := by
  simp [slots, i.isLt]

theorem slots_update (words : Fin 6 → List Bool) (i : Fin 6) (word : List Bool) :
    Function.update (slots words) (Fin.castAdd 26 i) word =
      slots (Function.update words i word) := by
  funext j
  by_cases hj : j.val < 6
  · let k : Fin 6 := ⟨j.val, hj⟩
    have heq : j = Fin.castAdd 26 k := Fin.ext rfl
    conv_lhs => rw [heq]
    conv_rhs => rw [heq]
    simp only [Function.update_apply, slots_low, (Fin.castAdd_injective 6 26).eq_iff]
  · have hne : j ≠ Fin.castAdd 26 i := by
      intro h
      have hv := congrArg Fin.val h
      have := i.isLt
      simp only [Fin.val_castAdd] at hv
      omega
    simp [slots, hj, Function.update_of_ne hne]

@[simp] theorem slots_work5 (words : Fin 6 → List Bool) (i : Fin 5) :
    slots words (work5 i) = [] := by
  unfold slots
  split_ifs with h
  · have hv : (work5 i).val = 6 + i.val := rfl
    omega
  · rfl

@[simp] theorem slots_work6 (words : Fin 6 → List Bool) (i : Fin 6) :
    slots words (work6 i) = [] := by
  unfold slots
  split_ifs with h
  · have hv : (work6 i).val = 6 + i.val := rfl
    omega
  · rfl

@[simp] theorem slots_work13 (words : Fin 6 → List Bool) (i : Fin 13) :
    slots words (work13 i) = [] := by
  unfold slots
  split_ifs with h
  · have hv : (work13 i).val = 6 + i.val := rfl
    omega
  · rfl

def initialWords (input : List Bool) : Fin 6 → List Bool := ![input, [], [], [], [], []]

def initialData (input : List Bool) : Data := ⟨fun _ => false, slots (initialWords input)⟩

theorem initialData_eq (input : List Bool) :
    initialData input = StructuredProgram.ioState 0 input := by
  apply CounterForPrograms.data_ext
  · rfl
  · funext i
    fin_cases i <;> simp [initialData, slots, Fin.coe_ofNat_eq_mod, initialWords]

/-- Exact parameter construction. The returned words are physically retained on
ports1..5; all local scratch stacks are empty, and the original binary n survives. -/
theorem command_eval (input : List Bool) (hn : 20 ≤ toNat input) :
    ∃ (t : ℕ) (rf : Fin 8 → Bool) (words : Fin 6 → List Bool),
      Eval command t (initialData input) ⟨rf, slots words⟩ ∧
      words 0 = input ∧
      toNat (words 1) = sparsifyLambda (toNat input) ∧
      toNat (words 2) = sparsifyNu (toNat input) ∧
      toNat (words 3) = sparsifyNu (toNat input) ^ 2 ∧
      toNat (words 4) = Nat.sqrt (sparsifyLambda (toNat input)) ∧
      toNat (words 5) = sparsifySchedule (toNat input) ∧
      (words 5).length ≤ sparsifyLambda (toNat input) ∧
      t ≤ 10000000 * (toNat input + input.length + 6) ^ 3 := by
  let w0 := initialWords input
  let d0 := initialData input
  have hc1 := ArithmeticCalls.copyAt_eval (0 : Fin 32) 1 6 d0
    (by decide) (by decide) (by decide) (by rfl) (by rfl)
  let d1 := ArithmeticCalls.afterCopy 0 1 d0
  obtain ⟨t1, lambda, hl1, hv1, hlen1, ht1⟩ := clogAt_eval 1 (by decide) (by decide) d1
    (by simp [d1, ArithmeticCalls.afterCopy, d0, initialData, slots, Fin.coe_ofNat_eq_mod])
    (by simp [d1, ArithmeticCalls.afterCopy, d0, initialData, slots, Fin.coe_ofNat_eq_mod])
    (by simpa [d1, ArithmeticCalls.afterCopy, d0, initialData, slots, Fin.coe_ofNat_eq_mod, initialWords] using
      (show 0 < toNat input by omega))
  let w1 := Function.update w0 1 lambda
  let r1 := resetRegs d1.regs
  let d2 : Data := ⟨r1, slots w1⟩
  have hd2 : (⟨resetRegs d1.regs, Function.update d1.stacks 1 lambda⟩ : Data) = d2 := by
    apply CounterForPrograms.data_ext
    · rfl
    · simp only [d1, ArithmeticCalls.afterCopy, d0, initialData, Function.update_idem]
      exact slots_update w0 1 lambda
  rw [hd2] at hl1
  have hv1' : toNat lambda = sparsifyLambda (toNat input) := by
    simpa [d1, ArithmeticCalls.afterCopy, d0, initialData, slots, Fin.coe_ofNat_eq_mod, initialWords,
      sparsifyLambda] using hv1
  have hlen1' : lambda.length ≤ input.length + 1 := by
    simpa [d1, ArithmeticCalls.afterCopy, d0, initialData, slots, Fin.coe_ofNat_eq_mod, initialWords] using hlen1
  have ht1' : t1 ≤ 68 * (input.length + 2) ^ 2 := by
    simpa [d1, ArithmeticCalls.afterCopy, d0, initialData, slots, Fin.coe_ofNat_eq_mod, initialWords] using ht1
  have hc2 := ArithmeticCalls.copyAt_eval (1 : Fin 32) 2 6 d2
    (by decide) (by decide) (by decide)
    (by simp [d2, slots, Fin.coe_ofNat_eq_mod, w1, w0, initialWords])
    (by simp [d2, slots, Fin.coe_ofNat_eq_mod])
  let d3 := ArithmeticCalls.afterCopy 1 2 d2
  obtain ⟨t2, nu, hl2, hv2, hlen2, ht2⟩ := clogAt_eval 2 (by decide) (by decide) d3
    (by simp [d3, ArithmeticCalls.afterCopy, d2, slots, Fin.coe_ofNat_eq_mod])
    (by simp [d3, ArithmeticCalls.afterCopy, d2, slots, Fin.coe_ofNat_eq_mod])
    (by
      have hpos : 0 < sparsifyLambda (toNat input) := Nat.clog_pos (by decide) (by omega)
      simpa [d3, ArithmeticCalls.afterCopy, d2, slots, Fin.coe_ofNat_eq_mod, w1, hv1'] using hpos)
  let w2 := Function.update w1 2 nu
  let r2 := resetRegs d3.regs
  let d4 : Data := ⟨r2, slots w2⟩
  have hd4 : (⟨resetRegs d3.regs, Function.update d3.stacks 2 nu⟩ : Data) = d4 := by
    apply CounterForPrograms.data_ext
    · rfl
    · simp only [d3, ArithmeticCalls.afterCopy, d2, Function.update_idem]
      exact slots_update w1 2 nu
  rw [hd4] at hl2
  have hv2' : toNat nu = sparsifyNu (toNat input) := by
    simpa [d3, ArithmeticCalls.afterCopy, d2, slots, Fin.coe_ofNat_eq_mod, w1, hv1', sparsifyNu] using hv2
  have hlen2' : nu.length ≤ input.length + 2 := by
    have : nu.length ≤ lambda.length + 1 := by
      simpa [d3, ArithmeticCalls.afterCopy, d2, slots, Fin.coe_ofNat_eq_mod, w1] using hlen2
    omega
  have ht2' : t2 ≤ 68 * (lambda.length + 2) ^ 2 := by
    simpa [d3, ArithmeticCalls.afterCopy, d2, slots, Fin.coe_ofNat_eq_mod, w1] using ht2
  obtain ⟨tm, rm, square, hm, hvm, hlenm, htm⟩ := ArithmeticCalls.multiplyAt_eval squarePorts d4
    ⟨by simp [d4, slots, Fin.coe_ofNat_eq_mod, w2, w1, w0, initialWords, squarePorts],
      by intro i; simp [d4, squarePorts]⟩
  let w3 := Function.update w2 3 square
  let d5 : Data := ⟨rm, slots w3⟩
  have hd5 : (⟨rm, Function.update d4.stacks squarePorts.out square⟩ : Data) = d5 := by
    apply CounterForPrograms.data_ext
    · rfl
    · exact slots_update w2 3 square
  rw [hd5] at hm
  have hvm' : toNat square = sparsifyNu (toNat input) ^ 2 := by
    simpa [squarePorts, d4, slots, Fin.coe_ofNat_eq_mod, w2, hv2', pow_two] using hvm
  have hlenm' : square.length ≤ 2 * input.length + 5 := by
    have : square.length ≤ nu.length + nu.length + 1 := by
      simpa [squarePorts, d4, slots, Fin.coe_ofNat_eq_mod, w2] using hlenm
    omega
  have htm' : tm ≤ 100 * (nu.length + nu.length + 1) ^ 2 := by
    simpa [squarePorts, d4, slots, Fin.coe_ofNat_eq_mod, w2] using htm
  obtain ⟨tr, rr, root, hr, hvr, hlenr, htr⟩ :=
    SqrtLog.LeafParameterArithmetic.sqrtAt_eval sqrtPorts d5
      ⟨by simp [sqrtPorts, d5, slots, Fin.coe_ofNat_eq_mod, w3, w2, w1, w0, initialWords],
        by intro i; simp [d5, sqrtPorts]⟩
  let w4 := Function.update w3 4 root
  let d6 : Data := ⟨rr, slots w4⟩
  have hd6 : (⟨rr, Function.update d5.stacks sqrtPorts.out root⟩ : Data) = d6 := by
    apply CounterForPrograms.data_ext
    · rfl
    · exact slots_update w3 4 root
  rw [hd6] at hr
  have hvr' : toNat root = Nat.sqrt (sparsifyLambda (toNat input)) := by
    simpa [sqrtPorts, d5, slots, Fin.coe_ofNat_eq_mod, w3, w2, w1, hv1'] using hvr
  have hlenr' : root.length ≤ sparsifyLambda (toNat input) := by
    simpa [sqrtPorts, d5, slots, Fin.coe_ofNat_eq_mod, w3, w2, w1, hv1'] using hlenr
  have htr' : tr ≤ 200001 * (sparsifyLambda (toNat input) + lambda.length + 2) ^ 3 := by
    simpa [sqrtPorts, d5, slots, Fin.coe_ofNat_eq_mod, w3, w2, w1, hv1'] using htr
  obtain ⟨tq, rq, result, hq, hvq, hlenq, htq⟩ :=
    SqrtLog.LeafParameterArithmetic.quotientAt_eval quotientPorts d6
      ⟨by simp [quotientPorts, d6, slots, Fin.coe_ofNat_eq_mod, w4, w3, w2, w1, w0, initialWords],
        by intro i; simp [d6, quotientPorts]⟩
      (by simpa [quotientPorts, d6, slots, Fin.coe_ofNat_eq_mod, w4, w3, hvm'] using
        (pow_pos (sparsifyNu_pos hn) 2))
  let w5 := Function.update w4 5 result
  have hd7 : (⟨rq, Function.update d6.stacks quotientPorts.out result⟩ : Data) =
      ⟨rq, slots w5⟩ := by
    apply CounterForPrograms.data_ext
    · rfl
    · exact slots_update w4 5 result
  rw [hd7] at hq
  have hvq' : toNat result = sparsifySchedule (toNat input) := by
    simpa [quotientPorts, d6, slots, Fin.coe_ofNat_eq_mod, w4, w3, hvr', hvm', sparsifySchedule] using hvq
  have hlenq' : result.length = root.length := by
    simpa [quotientPorts, d6, slots, Fin.coe_ofNat_eq_mod, w4] using hlenq
  have htq' : tq ≤ 150 * (root.length + square.length + 1) ^ 2 := by
    simpa [quotientPorts, d6, slots, Fin.coe_ofNat_eq_mod, w4, w3] using htq
  refine ⟨(7 * input.length + 5) + (t1 + ((7 * lambda.length + 5) +
    (t2 + (tm + (tr + tq))))), rq, w5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have he := hc1.seq (hl1.seq (hc2.seq (hl2.seq (hm.seq (hr.seq hq)))))
    simpa [command, d0, initialData, d2, slots, Fin.coe_ofNat_eq_mod, w1, w0, initialWords] using he
  · simp [w5, w4, w3, w2, w1, w0, initialWords]
  · simpa [w5, w4, w3, w2, w1] using hv1'
  · simpa [w5, w4, w3, w2] using hv2'
  · simpa [w5, w4, w3] using hvm'
  · simpa [w5, w4] using hvr'
  · simpa [w5] using hvq'
  · simpa [w5, hlenq'] using hlenr'
  · have hLambda : sparsifyLambda (toNat input) ≤ toNat input :=
      (Nat.le_pow_iff_clog_le (by decide : 1 < 2)).mp (Nat.lt_two_pow_self.le)
    let X := toNat input + input.length + 6
    have hX : 1 ≤ X := by dsimp [X]; omega
    have hsq : X ^ 2 ≤ X ^ 3 := by
      calc
        X ^ 2 = X ^ 2 * 1 := by simp
        _ ≤ X ^ 2 * X := Nat.mul_le_mul_left _ hX
        _ = X ^ 3 := by ring
    have hp1 := Nat.pow_le_pow_left (show input.length + 2 ≤ X by dsimp [X]; omega) 2
    have hp2 := Nat.pow_le_pow_left (show lambda.length + 2 ≤ X by dsimp [X]; omega) 2
    have hpm := Nat.pow_le_pow_left (show nu.length + nu.length + 1 ≤ 2 * X by
      dsimp [X]; omega) 2
    have hpr := Nat.pow_le_pow_left
      (show sparsifyLambda (toNat input) + lambda.length + 2 ≤ X by dsimp [X]; omega) 3
    have hpq := Nat.pow_le_pow_left (show root.length + square.length + 1 ≤ 2 * X by
      dsimp [X]; omega) 2
    have hlX : input.length ≤ X := by dsimp [X]; omega
    have hl1X : lambda.length ≤ X := by dsimp [X]; omega
    change _ ≤ 10000000 * X ^ 3
    nlinarith only [ht1', ht2', htm', htr', htq', hp1, hp2, hpm, hpr, hpq, hsq,
      hX, hlX, hl1X]


def program := compiled command 0 5

/-- The compiled local schedule has one actual trace and a uniform all-port,
every-prefix bound. The polynomial depends on n and the retained binary width. -/
theorem program_trace (input : List Bool) (hn : 20 ≤ toNat input) :
    ∃ (steps : ℕ) (rf : Fin 8 → Bool) (words : Fin 6 → List Bool),
      Trace program steps (initial program input) ((⟨rf, slots words⟩ : Data).withPC none) ∧
      words 0 = input ∧ toNat (words 5) = sparsifySchedule (toNat input) ∧
      (words 5).length ≤ sparsifyLambda (toNat input) ∧
      steps ≤ 10000001 * (toNat input + input.length + 6) ^ 3 ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps → Trace program prefixSteps (initial program input)
        intermediate → ∀ i,
        (intermediate.stacks i).length ≤
          input.length + 10000001 * (toNat input + input.length + 6) ^ 3 := by
  obtain ⟨t, rf, words, he, h0, _, _, _, _, h5, hlen, ht⟩ := command_eval input hn
  have htrace := compiled_halt_trace he (0 : Fin 32) 5
  rw [initialData_eq] at htrace
  change Trace program (t + 1) (initial program input)
    ((⟨rf, slots words⟩ : Data).withPC none) at htrace
  have htime : t + 1 ≤ 10000001 * (toNat input + input.length + 6) ^ 3 := by
    have hp : 1 ≤ (toNat input + input.length + 6) ^ 3 := by
      simpa using Nat.pow_le_pow_left
        (show 1 ≤ toNat input + input.length + 6 by omega) 3
    omega
  refine ⟨t + 1, rf, words, htrace, h0, h5, hlen, htime, ?_⟩
  intro prefixSteps intermediate hprefix hp i
  have hlocal := StructuredSpace.local_stack_bound program
    (steps := 10000001 * (toNat input + input.length + 6) ^ 3)
    (show dataBits (initial program input) ≤ input.length by simp)
  exact hlocal prefixSteps intermediate (hprefix.trans htime) hp i

/-- Fixed pre-DFS bank: input n267, retained schedule s266; remaining local ports
use their unchanged low indices. All off-bank caller data are framed. -/
def sharedStacks : Fin 32 ↪ Fin 1220 :=
  (Fin.castAddEmb 1188).trans
    ((Equiv.swap (0 : Fin 1220) 267).toEmbedding.trans
      (Equiv.swap (5 : Fin 1220) 266).toEmbedding)

@[simp] theorem sharedStacks_input : sharedStacks 0 = 267 := by
  decide

@[simp] theorem sharedStacks_output : sharedStacks 5 = 266 := by
  decide

theorem sharedStacks_other (i : Fin 32) (h0 : i ≠ 0) (h5 : i ≠ 5) :
    sharedStacks i = Fin.castAdd 1188 i := by
  have hzero : Fin.castAdd 1188 i ≠ (0 : Fin 1220) := by
    intro h
    apply h0
    have hv := congrArg (fun x : Fin 1220 => x.val) h
    exact Fin.ext hv
  have hfive : Fin.castAdd 1188 i ≠ (5 : Fin 1220) := by
    intro h
    apply h5
    have hv := congrArg (fun x : Fin 1220 => x.val) h
    exact Fin.ext hv
  have h267 : Fin.castAdd 1188 i ≠ (267 : Fin 1220) := by
    intro h; have hv := congrArg Fin.val h; have := i.isLt; change i.val = 267 at hv; omega
  have h266 : Fin.castAdd 1188 i ≠ (266 : Fin 1220) := by
    intro h; have hv := congrArg Fin.val h; have := i.isLt; change i.val = 266 at hv; omega
  change (Equiv.swap (5 : Fin 1220) 266)
    ((Equiv.swap (0 : Fin 1220) 267) (Fin.castAdd 1188 i)) = _
  rw [Equiv.swap_apply_of_ne_of_ne hzero h267, Equiv.swap_apply_of_ne_of_ne hfive h266]

def sharedCall : Cmd 80 1220 :=
  .call (ProgramLinking.liftProgram program (Fin.castAdd 72) sharedStacks)

def sharedProgram := ProgramLinking.liftProgram program (Fin.castAdd 72) sharedStacks

theorem sharedCall_eval (input : List Bool) (hn : 20 ≤ toNat input)
    (frame : State 80 1220) :
    ∃ (steps : ℕ) (rf : Fin 8 → Bool) (words : Fin 6 → List Bool),
      Eval sharedCall steps
        (embedState (Fin.castAdd 72) sharedStacks frame (StructuredProgram.ioState 0 input))
        (embedState (Fin.castAdd 72) sharedStacks frame ⟨rf, slots words⟩) ∧
      words 0 = input ∧ toNat (words 5) = sparsifySchedule (toNat input) ∧
      (words 5).length ≤ sparsifyLambda (toNat input) ∧
      steps ≤ 10000001 * (toNat input + input.length + 6) ^ 3 := by
  obtain ⟨steps, rf, words, ht, h0, h5, hlen, htime, _⟩ := program_trace input hn
  have hcall := eval_call_lifted program (Fin.castAdd 72) sharedStacks frame
    (Fin.castAdd_injective 8 72) sharedStacks.injective
    (a := StructuredProgram.ioState 0 input) (b := ⟨rf, slots words⟩) ht
  exact ⟨steps, rf, words, hcall, h0, h5, hlen, htime⟩

/-- Every retained caller stack contributes to the shared native schedule's
prefix bound; the bound is on the actual lifted trace. -/
theorem sharedProgram_trace (input : List Bool) (hn : 20 ≤ toNat input)
    (frame : State 80 1220) {D : ℕ} (hframe : ∀ i, (frame.stacks i).length ≤ D) :
    ∃ (steps : ℕ) (rf : Fin 8 → Bool) (words : Fin 6 → List Bool),
      Trace sharedProgram steps
        ((embedState (Fin.castAdd 72) sharedStacks frame
          (StructuredProgram.ioState 0 input)).withPC (some sharedProgram.entry))
        ((embedState (Fin.castAdd 72) sharedStacks frame ⟨rf, slots words⟩).withPC none) ∧
      words 0 = input ∧ toNat (words 5) = sparsifySchedule (toNat input) ∧
      (words 5).length ≤ sparsifyLambda (toNat input) ∧
      steps ≤ 10000001 * (toNat input + input.length + 6) ^ 3 ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace sharedProgram prefixSteps
          ((embedState (Fin.castAdd 72) sharedStacks frame
            (StructuredProgram.ioState 0 input)).withPC (some sharedProgram.entry))
          intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          max (input.length + 10000001 * (toNat input + input.length + 6) ^ 3) D := by
  obtain ⟨steps, rf, words, ht, h0, h5, hlen, htime, hlocal⟩ := program_trace input hn
  have htrace := ProgramLinking.liftProgram_trace program (Fin.castAdd 72) sharedStacks
    (frame.withPC none) (Fin.castAdd_injective 8 72) sharedStacks.injective ht
  have hspace := StructuredSpace.liftProgram_stack_bound program
    (Fin.castAdd 72) sharedStacks (frame.withPC none)
    (Fin.castAdd_injective 8 72) sharedStacks.injective ht hlocal hframe
  have hinputStack : program.inputStack = 0 := rfl
  simp only [initial, hinputStack] at htrace hspace
  refine ⟨steps, rf, words, ?_, h0, h5, hlen, htime, ?_⟩
  · simpa [sharedProgram, ProgramLinking.embedCfg, ProgramLinking.relocatePc,
      embedState, StructuredProgram.ioState, initial, StructuredProgram.State.withPC]
      using htrace
  · simpa [sharedProgram, ProgramLinking.embedCfg, ProgramLinking.relocatePc,
      embedState, StructuredProgram.ioState, initial, StructuredProgram.State.withPC]
      using hspace

private def resetPorts : List (Fin 80) → Cmd 80 1220
  | [] => .base .skip
  | i :: rest => .seq (.base (.atom (.set i false))) (resetPorts rest)

private def resetPortsState (ports : List (Fin 80)) (a : State 80 1220) : State 80 1220 :=
  ⟨fun i => if i ∈ ports then false else a.regs i, a.stacks⟩

private theorem resetPorts_eval (ports : List (Fin 80)) (a : State 80 1220) :
    Eval (resetPorts ports) ports.length a (resetPortsState ports a) := by
  induction ports generalizing a with
  | nil => simpa [resetPorts, resetPortsState] using (Eval.base (.skip a))
  | cons i rest ih =>
    have h := (Eval.base (StructuredProgram.Eval.atom (.set i false) a)).seq
      (ih ((StructuredProgram.Atom.set i false).eval a))
    convert h using 1
    · rfl
    · simp only [List.length_cons, Nat.add_comm]
    · apply CounterForPrograms.data_ext
      · funext j
        by_cases hj : j = i <;> by_cases hr : j ∈ rest <;>
          simp [resetPortsState, StructuredProgram.Atom.eval,
            StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
            execInstr, hj, hr]
      · rfl

/-- Eight fixed register writes discharge the concrete native caller's
arbitrary register contents before entering the schedule subroutine. -/
def resetShared : Cmd 80 1220 := resetPorts ((List.finRange 8).map (Fin.castAdd 72))

def resetSharedState (a : State 80 1220) : State 80 1220 :=
  resetPortsState ((List.finRange 8).map (Fin.castAdd 72)) a

theorem resetShared_eval (a : State 80 1220) : Eval resetShared 8 a (resetSharedState a) := by
  simpa [resetShared, resetSharedState] using
    resetPorts_eval ((List.finRange 8).map (Fin.castAdd 72)) a

@[simp] theorem resetSharedState_stacks (a : State 80 1220) :
    (resetSharedState a).stacks = a.stacks := rfl

@[simp] theorem resetSharedState_register (a : State 80 1220) (i : Fin 8) :
    (resetSharedState a).regs (Fin.castAdd 72 i) = false := by
  simp [resetSharedState, resetPortsState]

def readySharedCall : Cmd 80 1220 := .seq resetShared sharedCall

theorem readySharedCall_eval (input : List Bool) (hn : 20 ≤ toNat input)
    (a : State 80 1220)
    (hports : ∀ j : Fin 32, a.stacks (sharedStacks j) =
      if j = 0 then input else []) :
    ∃ (steps : ℕ) (rf : Fin 8 → Bool) (words : Fin 6 → List Bool),
      Eval readySharedCall steps a
        (embedState (Fin.castAdd 72) sharedStacks
          (resetSharedState a)
          ⟨rf, slots words⟩) ∧
      words 0 = input ∧ toNat (words 5) = sparsifySchedule (toNat input) ∧
      (words 5).length ≤ sparsifyLambda (toNat input) ∧
      steps ≤ 10000002 * (toNat input + input.length + 6) ^ 3 := by
  let frame := resetSharedState a
  have he : embedState (Fin.castAdd 72) sharedStacks frame
      (StructuredProgram.ioState 0 input) = frame := by
    apply embedState_eq_of_ports _ _ _ _ _ (Fin.castAdd_injective 8 72)
      sharedStacks.injective
    · intro i
      simp [frame]
    · intro i hi
      rfl
    · intro i
      exact hports i
    · intro i hi
      rfl
  obtain ⟨t, rf, words, ht, h0, h5, hlen, htime⟩ := sharedCall_eval input hn frame
  rw [he] at ht
  have hr : Eval resetShared 8 a frame := by
    exact resetShared_eval a
  refine ⟨8 + t, rf, words, hr.seq ht, h0, h5, hlen, ?_⟩
  have hcube : 8 ≤ (toNat input + input.length + 6) ^ 3 := by
    have h := Nat.pow_le_pow_left (show 2 ≤ toNat input + input.length + 6 by omega) 3
    norm_num at h ⊢
    exact h
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ScheduleProgram
