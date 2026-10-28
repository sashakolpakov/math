import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBlockParameterProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

open BitProgram StructuredCalls BinaryArithmetic

abbrev Regs := Fin 8 → Bool
abbrev Words := Fin 64 → List Bool
abbrev Data := StructuredProgram.State 8 77

def port (i : Fin 64) : Fin 77 := i.castAdd 13

def state (r : Regs) (w : Words) : Data :=
  ⟨r, fun i => if h : i.val < 64 then w ⟨i.val, h⟩ else []⟩

@[simp] theorem state_port (r : Regs) (w : Words) (i : Fin 64) :
    (state r w).stacks (port i) = w i := by simp [state, port]

theorem state_work (r : Regs) (w : Words) (i : Fin 77) (hi : 64 ≤ i.val) :
    (state r w).stacks i = [] := by simp [state, show ¬ i.val < 64 by omega]

theorem state_update (r rf : Regs) (w : Words) (i : Fin 64) (word : List Bool) :
    (⟨rf, Function.update (state r w).stacks (port i) word⟩ : Data) =
      state rf (Function.update w i word) := by
  apply CounterForPrograms.data_ext <;> try rfl
  funext j
  by_cases hj : j.val < 64
  · simp [state, Function.update_apply, port, hj, Fin.ext_iff]
  · have hji : j ≠ port i := by
      intro he
      have he' : j.val = i.val := congrArg (fun x : Fin 77 => x.val) he
      have hi := i.isLt
      omega
    simp [state, Function.update_apply, hj, hji]

def work (m : ℕ) (hm : m ≤ 13) : Fin m ↪ Fin 77 where
  toFun i := ⟨64 + i.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega

@[simp] theorem work_val (m : ℕ) (hm : m ≤ 13) (i : Fin m) :
    (work m hm i).val = 64 + i.val := rfl

theorem work_ne_port (m : ℕ) (hm : m ≤ 13) (i : Fin m) (j : Fin 64) :
    work m hm i ≠ port j := by
  intro h
  have he : 64 + i.val = j.val := congrArg (fun x : Fin 77 => x.val) h
  have := j.isLt
  omega

def arithmeticPorts (a b o : Fin 64) (hoa : o ≠ a) (hob : o ≠ b) :
    ArithmeticCalls.Ports 77 where
  left := port a
  right := port b
  out := port o
  work := work 5 (by decide)
  out_ne_left := by intro h; exact hoa ((Fin.castAdd_injective 64 13) h)
  out_ne_right := by intro h; exact hob ((Fin.castAdd_injective 64 13) h)
  work_ne_left := fun i => work_ne_port 5 (by decide) i a
  work_ne_right := fun i => work_ne_port 5 (by decide) i b
  work_ne_out := fun i => work_ne_port 5 (by decide) i o

def powerPorts (a b o : Fin 64) (hoa : o ≠ a) (hob : o ≠ b) :
    PowerCalls.Ports 77 where
  base := port a
  exponent := port b
  out := port o
  work := work 7 (by decide)
  out_ne_base := by intro h; exact hoa ((Fin.castAdd_injective 64 13) h)
  out_ne_exponent := by intro h; exact hob ((Fin.castAdd_injective 64 13) h)
  work_ne_base := fun i => work_ne_port 7 (by decide) i a
  work_ne_exponent := fun i => work_ne_port 7 (by decide) i b
  work_ne_out := fun i => work_ne_port 7 (by decide) i o

abbrev addCmd (a b o : Fin 64) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 77 :=
  ArithmeticCalls.addAt (arithmeticPorts a b o hoa hob)

abbrev multiplyCmd (a b o : Fin 64) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 77 :=
  ArithmeticCalls.multiplyAt (arithmeticPorts a b o hoa hob)

abbrev powerCmd (a b o : Fin 64) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 77 :=
  PowerCalls.powerAt (powerPorts a b o hoa hob)

theorem add_eval (r : Regs) (w : Words) (a b o : Fin 64)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ t rf word,
      Eval (addCmd a b o hoa hob) t (state r w)
        (state rf (Function.update w o word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w a) + BinaryArithmetic.toNat (w b) ∧
      word.length ≤ (w a).length + (w b).length + 1 ∧
      t ≤ 100 * ((w a).length + (w b).length + 1) ^ 2 := by
  have hv : ArithmeticCalls.Valid (arithmeticPorts a b o hoa hob) (state r w) := by
    constructor
    · simpa only [arithmeticPorts, state_port] using ho
    · intro i
      have hi : 64 ≤ (work 5 (by decide) i).val := by
        change 64 ≤ 64 + i.val
        omega
      exact state_work r w (work 5 (by decide) i) hi
  obtain ⟨t, rf, word, he, hval, hlen, htime⟩ :=
    ArithmeticCalls.addAt_eval (arithmeticPorts a b o hoa hob) (state r w) hv
  refine ⟨t, rf, word, ?_, ?_, ?_, ?_⟩
  · simpa only [addCmd, arithmeticPorts, state_update] using he
  · simpa only [arithmeticPorts, state_port] using hval
  · simpa only [arithmeticPorts, state_port] using hlen
  · simpa only [arithmeticPorts, state_port] using htime

theorem multiply_eval (r : Regs) (w : Words) (a b o : Fin 64)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ t rf word,
      Eval (multiplyCmd a b o hoa hob) t (state r w)
        (state rf (Function.update w o word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w a) * BinaryArithmetic.toNat (w b) ∧
      word.length ≤ (w a).length + (w b).length + 1 ∧
      t ≤ 100 * ((w a).length + (w b).length + 1) ^ 2 := by
  have hv : ArithmeticCalls.Valid (arithmeticPorts a b o hoa hob) (state r w) := by
    constructor
    · simpa only [arithmeticPorts, state_port] using ho
    · intro i
      have hi : 64 ≤ (work 5 (by decide) i).val := by
        change 64 ≤ 64 + i.val
        omega
      exact state_work r w (work 5 (by decide) i) hi
  obtain ⟨t, rf, word, he, hval, hlen, htime⟩ :=
    ArithmeticCalls.multiplyAt_eval (arithmeticPorts a b o hoa hob) (state r w) hv
  refine ⟨t, rf, word, ?_, ?_, ?_, ?_⟩
  · simpa only [multiplyCmd, arithmeticPorts, state_update] using he
  · simpa only [arithmeticPorts, state_port] using hval
  · simpa only [arithmeticPorts, state_port] using hlen
  · simpa only [arithmeticPorts, state_port] using htime

theorem power_eval (r : Regs) (w : Words) (a b o : Fin 64)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ t rf word,
      Eval (powerCmd a b o hoa hob) t (state r w)
        (state rf (Function.update w o word)) ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (w a) ^ BinaryArithmetic.toNat (w b) ∧
      word.length ≤ 1 + BinaryArithmetic.toNat (w b) * (w a).length ∧
      t ≤ PowerPrograms.runtimeBound (w a) (w b) + 9 * (w b).length + 8 := by
  have hv : PowerCalls.Valid (powerPorts a b o hoa hob) (state r w) := by
    constructor
    · simpa only [powerPorts, state_port] using ho
    · intro i
      have hi : 64 ≤ (work 7 (by decide) i).val := by
        change 64 ≤ 64 + i.val
        omega
      exact state_work r w (work 7 (by decide) i) hi
  obtain ⟨t, rf, word, he, hval, hlen, htime⟩ :=
    PowerCalls.powerAt_spec (powerPorts a b o hoa hob) (state r w) hv
  refine ⟨t, rf, word, ?_, ?_, ?_, ?_⟩
  · simpa only [powerCmd, powerPorts, state_update] using he
  · simpa only [powerPorts, state_port] using hval
  · simpa only [powerPorts, state_port] using hlen
  · simpa only [powerPorts, state_port] using htime

abbrev loadCmd (o : Fin 64) (word : List Bool) : Cmd 8 77 :=
  ArithmeticExpressionSupport.pushWord (port o) word

theorem load_eval (r : Regs) (w : Words) (o : Fin 64)
    (word : List Bool) (ho : w o = []) :
    ∃ rf, Eval (loadCmd o word) (2 * word.length) (state r w)
      (state rf (Function.update w o word)) := by
  obtain ⟨rf, he⟩ := ArithmeticExpressionSupport.pushWord_eval (port o) word (state r w)
  refine ⟨rf, ?_⟩
  simpa only [loadCmd, state_port, ho, List.append_nil, state_update] using he


end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

end OAI.Algorithms
