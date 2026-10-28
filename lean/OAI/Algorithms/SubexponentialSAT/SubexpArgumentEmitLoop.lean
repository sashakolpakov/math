import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpArgumentProgram
import OAI.Algorithms.SubexponentialSAT.SubexpArgumentKeyEmitter

namespace OAI.Algorithms

/-!
# Fixed control for emitting every term of an incidence argument

The coefficient stream contains beta, negative beta, then the row coefficients
in increasing row/coordinate order. It is a concatenation of coefficient frames.
The output list is built by prepending records and therefore has reverse order.

Runtime ports: 0 coefficient stream; 1 reversed key; 2 key-left counter;
3 output records; 4 key-right counter; 5 key-Z counter; 6 key-width counter;
7 preserved dimension; 8 preserved padded-key width; 9 column index;
10 columns after the current coordinate; 11 row degree; 12 columns remaining;
13 rows remaining; 14 copy scratch. Counters are unary Boolean stacks.
-/

namespace SubexponentialSAT.SubexpArgumentEmitLoop

open BitProgram StructuredCalls

abbrev atom (a : StructuredProgram.Atom 5 15) : Cmd 5 15 := .base (.atom a)

abbrev copyWord (src dst : Fin 15) : Cmd 5 15 :=
  .call (StackRoutines.copyProgram src dst 14 0 1)

abbrev clearWord (src : Fin 15) : Cmd 5 15 :=
  .call (StackRoutines.clearProgram src 0 1)

abbrev pushTrue (dst : Fin 15) : Cmd 5 15 :=
  .seq (atom (.set 0 true)) (atom (.push dst 0))

def keyRegisters (i : Fin 4) : Fin 5 := Fin.castAdd 1 i

def keyStacks (i : Fin 5) : Fin 15 :=
  match i.val with
  | 0 => 2
  | 1 => 4
  | 2 => 5
  | 3 => 6
  | _ => 1

def keyProgram := ProgramLinking.liftProgram SubexpArgumentKeyEmitter.program keyRegisters keyStacks

def termStacks (i : Fin 6) : Fin 15 := Fin.castAdd 9 i

def termProgram := ProgramLinking.liftProgram SubexpArgumentProgram.emitTermProgram id termStacks

abbrev emitPrepared : Cmd 5 15 := .seq (.call keyProgram) (.call termProgram)

abbrev emitConstant (u : Bool) : Cmd 5 15 :=
  .seq (atom (.set 2 false)) (.seq (atom (.set 3 u))
    (.seq (copyWord 7 2) (.seq (copyWord 8 6) emitPrepared)))

abbrev emitVariable : Cmd 5 15 :=
  .seq (copyWord 9 2) (.seq (copyWord 10 4) (.seq (copyWord 11 5)
    (.seq (copyWord 8 6) emitPrepared)))

abbrev columnBody : Cmd 5 15 :=
  .seq emitVariable (.seq (pushTrue 9)
    (.seq (atom (.pop 10 0 1)) (atom (.pop 12 0 1))))

abbrev columnLoop : Cmd 5 15 := .while 1 columnBody

abbrev rowBody : Cmd 5 15 :=
  .seq (clearWord 9) (.seq (copyWord 7 10) (.seq (atom (.pop 10 0 1))
    (.seq (copyWord 7 12) (.seq (atom (.pop 12 0 1)) (.seq columnLoop
      (.seq (pushTrue 11) (.seq (atom (.set 3 false)) (atom (.pop 13 0 1)))))))))

abbrev rowLoop : Cmd 5 15 := .while 1 rowBody

/-- This syntax has a fixed finite size, independent of D and row degree. -/
abbrev command : Cmd 5 15 :=
  .seq (emitConstant false) (.seq (emitConstant true)
    (.seq (atom (.set 2 true)) (.seq (atom (.set 3 true))
      (.seq (atom (.pop 13 0 1)) (.seq rowLoop (.seq (clearWord 9) (clearWord 11)))))))

def program := StructuredCalls.compiled command 0 3

theorem copyWord_eval (src dst : Fin 15) (hsd : src ≠ dst) (hs : src ≠ 14) (hd : dst ≠ 14)
    (d : State 5 15) (htmp : d.stacks 14 = []) :
    Eval (copyWord src dst) (7 * (d.stacks src).length + 5) d
      ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩ := by
  apply Eval.call
  exact ListRegisterProgram.copy_run src dst 14 0 1 hsd hs hd.symm (by decide) d.regs d.stacks htmp

theorem clearWord_eval (src : Fin 15) (d : State 5 15) :
    Eval (clearWord src) (2 * (d.stacks src).length + 3) d
      ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks src d.stacks⟩ := by
  apply Eval.call
  exact ListRegisterProgram.clear_run src 0 1 d.regs d.stacks

theorem keyRegisters_injective : Function.Injective keyRegisters := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 5 => x.val) h)

theorem keyStacks_injective : Function.Injective keyStacks := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [keyStacks]

theorem termStacks_injective : Function.Injective termStacks := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 15 => x.val) h)

def cells (input key left output right z width : List Bool) : Fin 7 → List Bool :=
  fun i => if i = 0 then input else if i = 1 then key else if i = 2 then left
    else if i = 3 then output else if i = 4 then right else if i = 5 then z else width

def world (regs : Fin 5 → Bool) (input key left output right z width : List Bool)
    (extra : Fin 8 → List Bool) : State 5 15 :=
  ⟨regs, Fin.addCases (motive := fun _ : Fin (7 + 8) => List Bool)
    (cells input key left output right z width) extra⟩

/-- Actual execution of key generation followed by record emission. The three
unary exponent counters and the width counter are consumed; all eight ports
outside this service's seven-port working area are preserved. -/
theorem emitPrepared_eval (left right z B : ℕ) (regs : Fin 5 → Bool)
    (coefficient tail output : List Bool) (extra : Fin 8 → List Bool) :
    Eval emitPrepared
      ((SubexpArgumentKeyEmitter.rawCost left right z (regs 2) (regs 3) +
        4 * (B - (SubexpArgumentKeyEmitter.rawKey left right z (regs 2) (regs 3)).length) + 3) +
        (29 * coefficient.length +
          21 * (SubexpArgumentKeyEmitter.paddedKey left right z B (regs 2) (regs 3)).length + 46))
      (world regs (Encoding.frame coefficient ++ tail) [] (List.replicate left true) output
        (List.replicate right true) (List.replicate z true) (List.replicate B true) extra)
      (world (SubexpArgumentProgram.finishedRegs regs) tail [] []
        (true :: (Encoding.frame (SubexpArgumentProgram.recordBody
          (SubexpArgumentKeyEmitter.paddedKey left right z B (regs 2) (regs 3)) coefficient) ++ output))
        [] [] [] extra) := by
  let key := SubexpArgumentKeyEmitter.paddedKey left right z B (regs 2) (regs 3)
  let start := world regs (Encoding.frame coefficient ++ tail) [] (List.replicate left true) output
    (List.replicate right true) (List.replicate z true) (List.replicate B true) extra
  let rr := readRegs regs 0 1 none
  let middle := world rr (Encoding.frame coefficient ++ tail) key.reverse [] output [] [] [] extra
  let finish := world (SubexpArgumentProgram.finishedRegs regs) tail [] []
    (true :: (Encoding.frame (SubexpArgumentProgram.recordBody key coefficient) ++ output)) [] [] [] extra
  let ka := SubexpArgumentKeyProgram.state (regs 0) (regs 1) (regs 2) (regs 3)
    (SubexpArgumentKeyEmitter.counters left right z) (List.replicate B true) []
  let kb := SubexpArgumentKeyProgram.state false false (regs 2) (regs 3)
    (SubexpArgumentKeyEmitter.counters 0 0 0) [] key.reverse
  have hka : embedState keyRegisters keyStacks start ka = start := by
    apply embedState_eq_of_ports _ _ _ _ _ keyRegisters_injective keyStacks_injective
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hkb : embedState keyRegisters keyStacks start kb = middle := by
    apply embedState_eq_of_ports _ _ _ _ _ keyRegisters_injective keyStacks_injective
    · intro i; fin_cases i <;> simp [kb, middle, world, rr, readRegs, keyRegisters,
        SubexpArgumentKeyProgram.state, SubexpArgumentKeyProgram.regs, SubexpPostfixControl.quadruple]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      simp [middle, start, world, rr, readRegs, h0, h1]
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h1 : i ≠ 1 := fun h => hi ⟨4, h.symm⟩
      have h2 : i ≠ 2 := fun h => hi ⟨0, h.symm⟩
      have h4 : i ≠ 4 := fun h => hi ⟨1, h.symm⟩
      have h5 : i ≠ 5 := fun h => hi ⟨2, h.symm⟩
      have h6 : i ≠ 6 := fun h => hi ⟨3, h.symm⟩
      fin_cases i <;> first | rfl | contradiction
  have kh := eval_call_lifted SubexpArgumentKeyEmitter.program keyRegisters keyStacks start
    keyRegisters_injective keyStacks_injective
    (SubexpArgumentKeyEmitter.program_trace left right z B (regs 0) (regs 1) (regs 2) (regs 3) [])
  have hk : Eval (.call keyProgram)
      (SubexpArgumentKeyEmitter.rawCost left right z (regs 2) (regs 3) +
        4 * (B - (SubexpArgumentKeyEmitter.rawKey left right z (regs 2) (regs 3)).length) + 3)
      start middle := by
    simp only [List.append_nil] at kh
    change Eval (.call keyProgram) _ (embedState keyRegisters keyStacks start ka)
      (embedState keyRegisters keyStacks start kb) at kh
    rw [hka, hkb] at kh
    exact kh
  let ta := SubexpRecordScan.recordState rr (Encoding.frame coefficient ++ tail) key.reverse [] output [] []
  let tb := SubexpRecordScan.recordState (SubexpArgumentProgram.finishedRegs rr) tail [] []
    (true :: (Encoding.frame (SubexpArgumentProgram.recordBody key coefficient) ++ output)) [] []
  have hta : embedState id termStacks middle ta = middle := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id termStacks_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i, rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have htb : embedState id termStacks middle tb = finish := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id termStacks_injective
    · intro i; fin_cases i <;> simp [tb, finish, world, rr, readRegs,
        SubexpArgumentProgram.finishedRegs]
    · intro i hi; exact (hi ⟨i, rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      have h3 : i ≠ 3 := fun h => hi ⟨3, h.symm⟩
      fin_cases i <;> first | rfl | contradiction
  have th := eval_call_lifted SubexpArgumentProgram.emitTermProgram id termStacks middle
    Function.injective_id termStacks_injective
    (SubexpArgumentProgram.emitTerm_trace key coefficient tail [] output rr)
  have ht : Eval (.call termProgram) (29 * coefficient.length + 21 * key.length + 46) middle finish := by
    change Eval (.call termProgram) _ (embedState id termStacks middle ta)
      (embedState id termStacks middle tb) at th
    rw [hta, htb] at th
    exact th
  exact Eval.seq hk ht

end SubexponentialSAT.SubexpArgumentEmitLoop

end OAI.Algorithms
