import OAI.Algorithms.SubexponentialSAT.ArithmeticCalls
import OAI.Algorithms.SubexponentialSAT.PowerCalls
import OAI.Algorithms.SubexponentialSAT.ArithmeticExpressionSupport
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryCompareProgram
import OAI.Algorithms.SubexponentialSAT.CounterPredProgram
import OAI.Algorithms.SubexponentialSAT.SaturatingSubtractionProgram

/-! Fixed Boolean-stack arithmetic in a 19-word data bank and 13 scratch stacks. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.ParametersProgram

open BitProgram StructuredCalls BinaryArithmetic

abbrev Regs := Fin 8 → Bool
abbrev Words := Fin 19 → List Bool
abbrev Data := StructuredProgram.State 8 32

def port (i : Fin 19) : Fin 32 := i.castAdd 13

theorem port_injective : Function.Injective port := Fin.castAdd_injective 19 13

@[simp] theorem port_inj {i j : Fin 19} : port i = port j ↔ i = j :=
  port_injective.eq_iff

def state (r : Regs) (w : Words) : Data :=
  ⟨r, fun i => if h : i.val < 19 then w ⟨i.val, h⟩ else []⟩

@[simp] theorem state_regs (r : Regs) (w : Words) : (state r w).regs = r := rfl

@[simp] theorem state_port (r : Regs) (w : Words) (i : Fin 19) :
    (state r w).stacks (port i) = w i := by simp [state, port]

theorem state_work (r : Regs) (w : Words) (i : Fin 32) (hi : 19 ≤ i.val) :
    (state r w).stacks i = [] := by simp [state, show ¬ i.val < 19 by omega]

theorem state_update (r rf : Regs) (w : Words) (i : Fin 19) (word : List Bool) :
    (⟨rf, Function.update (state r w).stacks (port i) word⟩ : Data) =
      state rf (Function.update w i word) := by
  apply CounterForPrograms.data_ext <;> try rfl
  funext j
  by_cases hj : j.val < 19
  · simp [state, Function.update_apply, port, hj, Fin.ext_iff]
  · have hji : j ≠ port i := by
      intro he
      have he' : j.val = i.val := congrArg (fun x : Fin 32 => x.val) he
      have hi := i.isLt
      omega
    simp [state, Function.update_apply, hj, hji]

def work (m : ℕ) (hm : m ≤ 13) : Fin m ↪ Fin 32 where
  toFun i := ⟨19 + i.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega

@[simp] theorem work_val (m : ℕ) (hm : m ≤ 13) (i : Fin m) :
    (work m hm i).val = 19 + i.val := rfl

theorem work_lower_bound (m : ℕ) (hm : m ≤ 13) (i : Fin m) :
    19 ≤ (work m hm i).val := by
  rw [work_val]
  omega

@[simp] theorem work_ne_port (m : ℕ) (hm : m ≤ 13) (i : Fin m) (j : Fin 19) :
    work m hm i ≠ port j := by
  intro h
  have he : 19 + i.val = j.val := congrArg (fun x : Fin 32 => x.val) h
  have := j.isLt
  omega

@[simp] theorem port_ne_work (m : ℕ) (hm : m ≤ 13) (i : Fin m) (j : Fin 19) :
    port j ≠ work m hm i := (work_ne_port m hm i j).symm

@[simp] theorem work_inj {m : ℕ} (hm hm' : m ≤ 13) {i j : Fin m} :
    work m hm i = work m hm' j ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg (fun x : Fin 32 => x.val) h
    simpa using hv
  · rintro rfl
    rfl

def arithmeticPorts (a b o : Fin 19) (hoa : o ≠ a) (hob : o ≠ b) :
    ArithmeticCalls.Ports 32 where
  left := port a
  right := port b
  out := port o
  work := work 5 (by decide)
  out_ne_left := by intro h; exact hoa ((Fin.castAdd_injective 19 13) h)
  out_ne_right := by intro h; exact hob ((Fin.castAdd_injective 19 13) h)
  work_ne_left := fun i => work_ne_port 5 (by decide) i a
  work_ne_right := fun i => work_ne_port 5 (by decide) i b
  work_ne_out := fun i => work_ne_port 5 (by decide) i o

def powerPorts (a b o : Fin 19) (hoa : o ≠ a) (hob : o ≠ b) :
    PowerCalls.Ports 32 where
  base := port a
  exponent := port b
  out := port o
  work := work 7 (by decide)
  out_ne_base := by intro h; exact hoa ((Fin.castAdd_injective 19 13) h)
  out_ne_exponent := by intro h; exact hob ((Fin.castAdd_injective 19 13) h)
  work_ne_base := fun i => work_ne_port 7 (by decide) i a
  work_ne_exponent := fun i => work_ne_port 7 (by decide) i b
  work_ne_out := fun i => work_ne_port 7 (by decide) i o

def addCmd (a b o : Fin 19) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 32 :=
  ArithmeticCalls.addAt (arithmeticPorts a b o hoa hob)

def multiplyCmd (a b o : Fin 19) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 32 :=
  ArithmeticCalls.multiplyAt (arithmeticPorts a b o hoa hob)

def powerCmd (a b o : Fin 19) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 32 :=
  PowerCalls.powerAt (powerPorts a b o hoa hob)

theorem add_eval (r : Regs) (w : Words) (a b o : Fin 19)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ t rf word,
      Eval (addCmd a b o hoa hob) t (state r w)
        (state rf (Function.update w o word)) ∧
      toNat word = toNat (w a) + toNat (w b) ∧
      word.length ≤ (w a).length + (w b).length + 1 ∧
      t ≤ 100 * ((w a).length + (w b).length + 1) ^ 2 := by
  have hv : ArithmeticCalls.Valid (arithmeticPorts a b o hoa hob) (state r w) := by
    constructor
    · simpa only [arithmeticPorts, state_port] using ho
    · intro i
      simpa only [arithmeticPorts] using
        state_work r w (work 5 (by decide) i) (work_lower_bound 5 (by decide) i)
  obtain ⟨t, rf, word, he, hval, hlen, htime⟩ :=
    ArithmeticCalls.addAt_eval (arithmeticPorts a b o hoa hob) (state r w) hv
  refine ⟨t, rf, word, ?_, ?_, ?_, ?_⟩
  · simpa only [addCmd, arithmeticPorts, state_update] using he
  · simpa only [arithmeticPorts, state_port] using hval
  · simpa only [arithmeticPorts, state_port] using hlen
  · simpa only [arithmeticPorts, state_port] using htime

theorem multiply_eval (r : Regs) (w : Words) (a b o : Fin 19)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ t rf word,
      Eval (multiplyCmd a b o hoa hob) t (state r w)
        (state rf (Function.update w o word)) ∧
      toNat word = toNat (w a) * toNat (w b) ∧
      word.length ≤ (w a).length + (w b).length + 1 ∧
      t ≤ 100 * ((w a).length + (w b).length + 1) ^ 2 := by
  have hv : ArithmeticCalls.Valid (arithmeticPorts a b o hoa hob) (state r w) := by
    constructor
    · simpa only [arithmeticPorts, state_port] using ho
    · intro i
      simpa only [arithmeticPorts] using
        state_work r w (work 5 (by decide) i) (work_lower_bound 5 (by decide) i)
  obtain ⟨t, rf, word, he, hval, hlen, htime⟩ :=
    ArithmeticCalls.multiplyAt_eval (arithmeticPorts a b o hoa hob) (state r w) hv
  refine ⟨t, rf, word, ?_, ?_, ?_, ?_⟩
  · simpa only [multiplyCmd, arithmeticPorts, state_update] using he
  · simpa only [arithmeticPorts, state_port] using hval
  · simpa only [arithmeticPorts, state_port] using hlen
  · simpa only [arithmeticPorts, state_port] using htime

theorem power_eval (r : Regs) (w : Words) (a b o : Fin 19)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ t rf word,
      Eval (powerCmd a b o hoa hob) t (state r w)
        (state rf (Function.update w o word)) ∧
      toNat word = toNat (w a) ^ toNat (w b) ∧
      word.length ≤ 1 + toNat (w b) * (w a).length ∧
      t ≤ PowerPrograms.runtimeBound (w a) (w b) + 9 * (w b).length + 8 := by
  have hv : PowerCalls.Valid (powerPorts a b o hoa hob) (state r w) := by
    constructor
    · simpa only [powerPorts, state_port] using ho
    · intro i
      simpa only [powerPorts] using
        state_work r w (work 7 (by decide) i) (work_lower_bound 7 (by decide) i)
  obtain ⟨t, rf, word, he, hval, hlen, htime⟩ :=
    PowerCalls.powerAt_spec (powerPorts a b o hoa hob) (state r w) hv
  refine ⟨t, rf, word, ?_, ?_, ?_, ?_⟩
  · simpa only [powerCmd, powerPorts, state_update] using he
  · simpa only [powerPorts, state_port] using hval
  · simpa only [powerPorts, state_port] using hlen
  · simpa only [powerPorts, state_port] using htime

def loadCmd (o : Fin 19) (word : List Bool) : Cmd 8 32 :=
  ArithmeticExpressionSupport.pushWord (port o) word

theorem load_eval (r : Regs) (w : Words) (o : Fin 19)
    (word : List Bool) (ho : w o = []) :
    ∃ rf, Eval (loadCmd o word) (2 * word.length) (state r w)
      (state rf (Function.update w o word)) := by
  obtain ⟨rf, he⟩ := ArithmeticExpressionSupport.pushWord_eval (port o) word (state r w)
  refine ⟨rf, ?_⟩
  simpa only [loadCmd, state_port, ho, List.append_nil, state_update] using he




def copyCmd (a o : Fin 19) : Cmd 8 32 :=
  ArithmeticCalls.copyAt (port a) (port o) (work 1 (by decide) 0)

theorem copy_eval (r : Regs) (w : Words) (a o : Fin 19) (hoa : o ≠ a) (ho : w o = []) :
    ∃ rf, Eval (copyCmd a o) (7*(w a).length+5) (state r w)
        (state rf (Function.update w o (w a))) := by
  have hh := ArithmeticCalls.copyAt_eval (port a) (port o) (work 1 (by decide) 0) (state r w)
    (by intro h; exact hoa ((Fin.castAdd_injective 19 13) h.symm))
    (work_ne_port 1 (by decide) 0 a).symm
    (work_ne_port 1 (by decide) 0 o)
    (by simpa using ho)
    (state_work r w (work 1 (by decide) 0) (work_lower_bound 1 (by decide) 0))
  refine ⟨readRegs r 0 1 none, ?_⟩
  simpa only [copyCmd, ArithmeticCalls.afterCopy, state_regs, state_port, state_update] using hh


def clearCmd (a : Fin 19) : Cmd 8 32 :=
  ArithmeticExpressionSupport.clearCmd (port a)

theorem clear_eval (r : Regs) (w : Words) (a : Fin 19) :
    ∃ rf, Eval (clearCmd a) (2 * (w a).length + 3) (state r w)
      (state rf (Function.update w a [])) := by
  have h := ArithmeticExpressionSupport.clear_eval (port a) (state r w)
  refine ⟨readRegs r 0 1 none, ?_⟩
  simpa only [clearCmd, state_regs, state_port, state_update] using h

def logRegisters : Fin 3 → Fin 8 := Fin.castAdd 5

def logStacks (a : Fin 19) : Fin 3 → Fin 32 :=
  ![port a, work 2 (by decide) 0, work 2 (by decide) 1]

theorem logRegisters_injective : Function.Injective logRegisters :=
  Fin.castAdd_injective 3 5

theorem logStacks_injective (a : Fin 19) : Function.Injective (logStacks a) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [logStacks]

/-- Reset the local logarithm program's three Boolean registers. -/
def resetLogRegisters : Cmd 8 32 :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.set 1 false))) (.base (.atom (.set 2 false))))

/-- The input word is preserved and the logarithm overwrites its fresh copy. -/
def clogCmd (a o : Fin 19) : Cmd 8 32 :=
  .seq (copyCmd a o) (.seq resetLogRegisters
    (.call (ProgramLinking.liftProgram
      OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.program logRegisters (logStacks o))))

def zeroLogRegs (r : Regs) : Regs :=
  Function.update (Function.update (Function.update r 0 false) 1 false) 2 false

theorem resetLogRegisters_eval (r : Regs) (w : Words) :
    Eval resetLogRegisters 3 (state r w) (state (zeroLogRegs r) w) := by
  have h0 := StructuredProgram.Eval.atom (.set (0 : Fin 8) false) (state r w)
  have h1 := StructuredProgram.Eval.atom (.set (1 : Fin 8) false)
    ((StructuredProgram.Atom.set (0 : Fin 8) false).eval (state r w))
  have h2 := StructuredProgram.Eval.atom (.set (2 : Fin 8) false)
    ((StructuredProgram.Atom.set (1 : Fin 8) false).eval
      ((StructuredProgram.Atom.set (0 : Fin 8) false).eval (state r w)))
  simpa [resetLogRegisters, zeroLogRegs, state, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using
    (Eval.base h0).seq ((Eval.base h1).seq (Eval.base h2))

theorem zeroLogRegs_logRegisters (r : Regs) (i : Fin 3) :
    zeroLogRegs r (logRegisters i) = false := by
  fin_cases i <;> simp [zeroLogRegs, logRegisters]

theorem log_call_eval (r : Regs) (w : Words) (a : Fin 19)
    (hr : ∀ i : Fin 3, r (logRegisters i) = false) (ha : 0 < toNat (w a)) :
    ∃ t output, Eval (.call (ProgramLinking.liftProgram
        OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.program logRegisters (logStacks a)))
      t (state r w) (state r (Function.update w a output)) ∧
      toNat output = Nat.clog 2 (toNat (w a)) ∧
      output.length ≤ (w a).length + 1 ∧ t ≤ 65 * ((w a).length + 2) ^ 2 := by
  obtain ⟨output, hv, hl, t, ht, he⟩ :=
    OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.program_runs (w a)
      (by simpa only [CounterPrograms.value_eq_toNat] using ha)
  have hproj : projectState logRegisters (logStacks a) (state r w) =
      (StructuredProgram.ioState (0 : Fin 3) (w a) : StructuredProgram.State 3 3) := by
    apply CounterForPrograms.data_ext
    · funext i
      exact hr i
    · funext i
      fin_cases i
      · change (state r w).stacks (port a) = w a
        exact state_port r w a
      · change (state r w).stacks (work 2 (by decide) 0) = []
        exact state_work r w _ (work_lower_bound 2 (by decide) 0)
      · change (state r w).stacks (work 2 (by decide) 1) = []
        exact state_work r w _ (work_lower_bound 2 (by decide) 1)
  have htrace : Trace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.program t
      ((StructuredProgram.ioState (0 : Fin 3) (w a)).withPC
        (some OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.program.entry))
      ((StructuredProgram.ioState (0 : Fin 3) output).withPC none) := by
    change Trace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.program t
      (initial OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.program (w a))
      (terminal OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.program output)
    exact he
  have hc := eval_call_from_state
    OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.program logRegisters (logStacks a)
    (state r w) logRegisters_injective (logStacks_injective a)
    (b := StructuredProgram.ioState (0 : Fin 3) output) (by rw [hproj]; exact htrace)
  have hend : embedState logRegisters (logStacks a) (state r w)
      (StructuredProgram.ioState (0 : Fin 3) output) =
      state r (Function.update w a output) := by
    rw [← state_update r r w a output]
    apply embedState_eq_of_ports _ _ _ _ _ logRegisters_injective (logStacks_injective a)
    · intro i
      exact hr i
    · intro i _
      rfl
    · intro i
      fin_cases i
      · change Function.update (state r w).stacks (port a) output (port a) = output
        exact Function.update_self _ _ _
      · change Function.update (state r w).stacks (port a) output (work 2 (by decide) 0) = []
        rw [Function.update_of_ne (work_ne_port 2 (by decide) 0 a)]
        exact state_work r w _ (by decide)
      · change Function.update (state r w).stacks (port a) output (work 2 (by decide) 1) = []
        rw [Function.update_of_ne (work_ne_port 2 (by decide) 1 a)]
        exact state_work r w _ (by decide)
    · intro i hi
      have hne : i ≠ port a := by
        intro h
        exact hi ⟨0, h.symm⟩
      simp [hne]
  rw [hend] at hc
  exact ⟨t, output, hc, by simpa only [CounterPrograms.value_eq_toNat] using hv, hl, ht⟩

theorem clog_eval (r : Regs) (w : Words) (a o : Fin 19) (hoa : o ≠ a)
    (ho : w o = []) (ha : 0 < toNat (w a)) :
    ∃ t rf output, Eval (clogCmd a o) t (state r w)
        (state rf (Function.update w o output)) ∧
      toNat output = Nat.clog 2 (toNat (w a)) ∧
      output.length ≤ (w a).length + 1 ∧ t ≤ 80 * ((w a).length + 2) ^ 2 := by
  obtain ⟨rf, hc⟩ := copy_eval r w a o hoa ho
  have hz := resetLogRegisters_eval rf (Function.update w o (w a))
  obtain ⟨t, output, hl, hv, hlen, ht⟩ := log_call_eval (zeroLogRegs rf)
    (Function.update w o (w a)) o (zeroLogRegs_logRegisters rf)
    (by simpa using ha)
  refine ⟨(7 * (w a).length + 5) + (3 + t), zeroLogRegs rf, output, ?_, ?_, ?_, ?_⟩
  · simpa [clogCmd, Function.update_idem] using hc.seq (hz.seq hl)
  · simpa using hv
  · simpa using hlen
  · simp only [Function.update_self] at ht
    nlinarith

def compareStacks (a b : Fin 19) : Fin 2 → Fin 32 := ![port a, port b]

/-- Consumes both selected words and returns their strict comparison in register zero. -/
def compareCmd (a b : Fin 19) : Cmd 8 32 :=
  .call (ProgramLinking.liftProgram OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryCompareProgram.Compare.program id
    (compareStacks a b))

theorem compareStacks_injective {a b : Fin 19} (hab : a ≠ b) :
    Function.Injective (compareStacks a b) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [compareStacks, port, Fin.ext_iff]

theorem compare_eval (r : Regs) (w : Words) (a b : Fin 19) (hab : a ≠ b) :
    ∃ rf, Eval (compareCmd a b) (10 * max (w a).length (w b).length + 6)
        (state r w) (state rf (Function.update (Function.update w a []) b [])) ∧
      (rf 0 = true ↔ toNat (w a) < toNat (w b)) := by
  obtain ⟨out, he, hv, _, hf, hz⟩ := OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryCompareProgram.compare_call id
    (compareStacks a b) Function.injective_id (compareStacks_injective hab) (state r w)
  have hout : out = state out.regs (Function.update (Function.update w a []) b []) := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext i
      by_cases ha : i = port a
      · subst i
        simpa [compareStacks, state, port, hab, Ne.symm hab] using hz 0
      · by_cases hb : i = port b
        · subst i
          simpa [compareStacks, state, port] using hz 1
        · have hi : ¬ ∃ j, compareStacks a b j = i := by
            rintro ⟨j, hj⟩
            fin_cases j <;> simp_all [compareStacks]
          rw [hf i hi]
          simp only [state]
          split_ifs with h
          · have hia : (⟨i.val, h⟩ : Fin 19) ≠ a := by
              intro e
              apply ha
              exact Fin.ext (congrArg (fun x : Fin 19 => x.val) e)
            have hib : (⟨i.val, h⟩ : Fin 19) ≠ b := by
              intro e
              apply hb
              exact Fin.ext (congrArg (fun x : Fin 19 => x.val) e)
            simp [hia, hib]
          · rfl
  rw [hout] at he
  refine ⟨out.regs, ?_, ?_⟩
  · simpa [compareCmd, compareStacks] using he
  · simpa [compareStacks] using hv

def predPorts (a : Fin 19) : CounterForPrograms.Ports 8 32 where
  register := ⟨logRegisters, logRegisters_injective⟩
  counter := port a
  scratch := work 1 (by decide) 0
  counter_ne_scratch := (work_ne_port 1 (by decide) 0 a).symm

def predCmd (a : Fin 19) : Cmd 8 32 := CounterPredProgram.predCmd (predPorts a)

theorem pred_eval (r : Regs) (w : Words) (a : Fin 19) :
    ∃ t rf word, Eval (predCmd a) t (state r w)
        (state rf (Function.update w a word)) ∧
      toNat word = toNat (w a) - 1 ∧ word.length ≤ (w a).length ∧
      t ≤ 20 * ((w a).length + 1) := by
  obtain ⟨t,rf,word,ht,he,hv,hl⟩ := CounterPredProgram.pred_correct (predPorts a) (state r w)
    (by simpa only [predPorts] using
      state_work r w (work 1 (by decide) 0) (work_lower_bound 1 (by decide) 0))
  exact ⟨t,rf,word,by simpa only [predCmd,predPorts,state_update] using he,
    by simpa only [predPorts,state_port] using hv,
    by simpa only [predPorts,state_port] using hl,
    by simpa only [predPorts,state_port] using ht⟩

def subtractStacks (a b o : Fin 19) : Fin 8 → Fin 32 :=
  ![port a, port b, port o, work 5 (by decide) 0, work 5 (by decide) 1,
    work 5 (by decide) 2, work 5 (by decide) 3, work 5 (by decide) 4]

theorem subtractStacks_injective {a b o : Fin 19}
    (hab : a ≠ b) (hoa : o ≠ a) (hob : o ≠ b) :
    Function.Injective (subtractStacks a b o) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [subtractStacks]

def subtractBlock (a b o : Fin 19) (hab : a ≠ b) (hoa : o ≠ a) (hob : o ≠ b) :
    Fin 8 ↪ Fin 32 := ⟨subtractStacks a b o, subtractStacks_injective hab hoa hob⟩

def subtractCmd (a b o : Fin 19) (hab : a ≠ b) (hoa : o ≠ a) (hob : o ≠ b) :
    Cmd 8 32 :=
  .call (ProgramLinking.liftProgram
    (compiled SaturatingSubtractionProgram.command 0 2) id (subtractBlock a b o hab hoa hob))

theorem subtract_eval (r : Regs) (w : Words) (a b o : Fin 19)
    (hab : a ≠ b) (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ t output, Eval (subtractCmd a b o hab hoa hob) t (state r w)
        (state (fun _ => false) (Function.update w o output)) ∧
      toNat output = toNat (w a) - toNat (w b) ∧
      output.length ≤ (w a).length + (w b).length ∧
      t ≤ 100 * ((w a).length + (w b).length + 1) := by
  obtain ⟨t, output, ht, he, hv, hl⟩ := SaturatingSubtractionProgram.command_eval r (w a) (w b)
  have hproj : (SaturatingSubtractionProgram.state r (w a) (w b) []).stacks =
      (state r w).stacks ∘ subtractBlock a b o hab hoa hob := by
    funext i
    fin_cases i
    · change w a = (state r w).stacks (port a)
      exact (state_port r w a).symm
    · change w b = (state r w).stacks (port b)
      exact (state_port r w b).symm
    · change [] = (state r w).stacks (port o)
      rw [state_port, ho]
    · change [] = (state r w).stacks (work 5 (by decide) 0)
      exact (state_work r w _ (work_lower_bound 5 (by decide) 0)).symm
    · change [] = (state r w).stacks (work 5 (by decide) 1)
      exact (state_work r w _ (work_lower_bound 5 (by decide) 1)).symm
    · change [] = (state r w).stacks (work 5 (by decide) 2)
      exact (state_work r w _ (work_lower_bound 5 (by decide) 2)).symm
    · change [] = (state r w).stacks (work 5 (by decide) 3)
      exact (state_work r w _ (work_lower_bound 5 (by decide) 3)).symm
    · change [] = (state r w).stacks (work 5 (by decide) 4)
      exact (state_work r w _ (work_lower_bound 5 (by decide) 4)).symm
  have hout : (SaturatingSubtractionProgram.state (fun _ => false) (w a) (w b) output).stacks =
      Function.update (SaturatingSubtractionProgram.state r (w a) (w b) []).stacks 2 output := by
    funext i
    fin_cases i <;> simp
  have hc := ArithmeticExpressionSupport.call_on_block SaturatingSubtractionProgram.command 0 2
    (subtractBlock a b o hab hoa hob) (state r w)
    (SaturatingSubtractionProgram.state r (w a) (w b) [])
    (SaturatingSubtractionProgram.state (fun _ => false) (w a) (w b) output)
    output he rfl hproj hout
  refine ⟨t + 1, output, ?_, hv, hl, ht⟩
  change Eval (subtractCmd a b o hab hoa hob) (t + 1) (state r w)
    (⟨(fun _ => false), Function.update (state r w).stacks (port o) output⟩ : Data) at hc
  rw [state_update] at hc
  exact hc

/-- A padded binary input still bounds its ceiling logarithm by its bit length. -/
theorem clog_le_word_length (word : List Bool) :
    Nat.clog 2 (toNat word) ≤ word.length := by
  apply (Nat.le_pow_iff_clog_le (by decide : 1 < 2)).mp
  have h := OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Floor.value_lt_two_pow_length word
  rw [CounterPrograms.value_eq_toNat] at h
  exact h.le

theorem clog_le_input (n : ℕ) : Nat.clog 2 n ≤ n :=
  (Nat.le_pow_iff_clog_le (by decide : 1 < 2)).mp Nat.lt_two_pow_self.le

/-- Exponentiation is polynomial here because both the numerical exponent and
all actual operand lengths are bounded. -/
theorem power_eval_bounded (r : Regs) (w : Words) (a b o : Fin 19)
    (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) (B : ℕ)
    (ha : (w a).length ≤ B) (hb : (w b).length ≤ B) (hv : toNat (w b) ≤ B) :
    ∃ t rf word, Eval (powerCmd a b o hoa hob) t (state r w)
        (state rf (Function.update w o word)) ∧
      toNat word = toNat (w a) ^ toNat (w b) ∧
      word.length ≤ (B + 1) ^ 2 ∧ t ≤ 100 * (B + 2) ^ 4 := by
  obtain ⟨t,rf,word,he,hval,hlen,ht⟩ := power_eval r w a b o hoa hob ho
  refine ⟨t,rf,word,he,hval,?_,?_⟩
  · have hm := Nat.mul_le_mul hv ha
    nlinarith
  · have hbound : PowerPrograms.runtimeBound (w a) (w b) + 9 * (w b).length + 8 ≤
        B * (50 * (B + 1) * (2 + (B + 1) * B)) +
          (B + 1) * (16 * B + 16) + 3 + 9 * B + 8 := by
      unfold PowerPrograms.runtimeBound PowerPrograms.workBound PowerPrograms.callbackBound
      gcongr
    have hpol : B * (50 * (B + 1) * (2 + (B + 1) * B)) +
        (B + 1) * (16 * B + 16) + 3 + 9 * B + 8 ≤ 100 * (B + 2) ^ 4 := by
      nlinarith [Nat.zero_le (B ^ 3), Nat.zero_le (B ^ 4)]
    exact ht.trans (hbound.trans hpol)

/-- Sequential composition of a fixed finite list of commands. -/
def sequence : List (Cmd 8 32) → Cmd 8 32
  | [] => .base .skip
  | c :: cs => .seq c (sequence cs)

def clearedWords (ports : List (Fin 19)) (w : Words) : Words :=
  fun i => if i ∈ ports then [] else w i

theorem clearSequence_eval (ports : List (Fin 19)) (r : Regs) (w : Words) (B : ℕ)
    (hwidth : ∀ i, (w i).length ≤ B) :
    ∃ t rf, Eval (sequence (ports.map clearCmd)) t (state r w)
        (state rf (clearedWords ports w)) ∧ t ≤ ports.length * (2 * B + 3) := by
  induction ports generalizing r w with
  | nil =>
    refine ⟨0,r,?_,by simp⟩
    have hclear : clearedWords [] w = w := by
      funext i
      simp [clearedWords]
    rw [hclear]
    exact Eval.base (StructuredProgram.Eval.skip (state r w))
  | cons p ps ih =>
    obtain ⟨r₁,h₁⟩ := clear_eval r w p
    have hnext : ∀ i, (Function.update w p [] i).length ≤ B := by
      intro i
      by_cases hi : i = p
      · subst i
        simp
      · rw [Function.update_of_ne hi]
        exact hwidth i
    obtain ⟨t,rf,he,ht⟩ := ih r₁ (Function.update w p []) hnext
    have hfinal : clearedWords ps (Function.update w p []) = clearedWords (p :: ps) w := by
      funext i
      by_cases hi : i = p
      · subst i
        simp [clearedWords]
      · simp [clearedWords, hi]
    refine ⟨(2 * (w p).length + 3) + t,rf,?_,?_⟩
    · simpa only [List.map_cons, sequence, hfinal] using h₁.seq he
    · simp only [List.length_cons]
      nlinarith [hwidth p]


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.ParametersProgram
