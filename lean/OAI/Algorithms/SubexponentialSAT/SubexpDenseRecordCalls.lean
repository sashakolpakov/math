import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseProgram

namespace OAI.Algorithms

/-! Exact physical call interfaces for the two fixed record routines used by
the nested multiplication loops. Only their named ports may change. -/

namespace SubexponentialSAT.SubexpDenseRecordCalls

open BitProgram StructuredCalls SubexpDenseProgram SubexpRecordScan

abbrev Data := State 16 128

def registers : Fin 5 ↪ Fin 16 := ⟨Fin.castAdd 11, by
  intro a b h
  apply Fin.ext
  exact congrArg (fun i : Fin 16 => i.val) h⟩

abbrev parse (ports : Fin 6 ↪ Fin 128) : Cmd 16 128 :=
  .call (ProgramLinking.liftProgram RawParser.unpackProgram registers ports)

def parsedStacks (ports : Fin 6 ↪ Fin 128) (key coefficient : List Bool)
    (stk : Fin 128 → List Bool) : Fin 128 → List Bool :=
  Function.update (Function.update (Function.update stk (ports 0) [])
    (ports 1) key) (ports 2) coefficient

theorem parse_eval (ports : Fin 6 ↪ Fin 128) (d : Data) (key coefficient : List Bool)
    (hin : d.stacks (ports 0) = (SubexpArgumentProgram.recordBody key coefficient).reverse)
    (h1 : d.stacks (ports 1) = []) (h2 : d.stacks (ports 2) = [])
    (h3 : d.stacks (ports 3) = []) (h4 : d.stacks (ports 4) = []) :
    ∃ e : Data, Eval (parse ports) (15*key.length+15*coefficient.length+24) d e ∧
      e.stacks = parsedStacks ports key coefficient d.stacks := by
  let rs : Fin 5 → Bool := fun i => d.regs (registers i)
  let a := recordState rs (SubexpArgumentProgram.recordBody key coefficient).reverse
    [] [] [] [] (d.stacks (ports 5))
  let b := recordState (readRegs rs 0 1 none) [] key coefficient [] [] (d.stacks (ports 5))
  have ha : embedState registers ports d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ registers.injective ports.injective
    · intro i; rfl
    · intros; rfl
    · intro i
      fin_cases i <;> first | exact hin | exact h1 | exact h2 | exact h3 | exact h4 | rfl
    · intros; rfl
  let e := embedState registers ports d b
  have ht := eval_call_lifted RawParser.unpackProgram registers ports d
    registers.injective ports.injective (RawParser.unpack_trace rs key coefficient (d.stacks (ports 5)))
  change Eval (parse ports) _ (embedState registers ports d a) e at ht
  refine ⟨e, ?_, ?_⟩
  · simpa only [ha] using ht
  · funext i
    have heq (j k : Fin 6) : ports j = ports k ↔ j = k := ports.injective.eq_iff
    by_cases hi : ∃ j, ports j = i
    · obtain ⟨j, rfl⟩ := hi
      change (embedState registers ports d b).stacks (ports j) = _
      rw [embedState_stack _ _ _ _ ports.injective]
      fin_cases j <;> simp [b, storage, parsedStacks, heq, h3, h4]
    · change (embedState registers ports d b).stacks i = _
      rw [embedState_stack_frame _ _ _ _ _ hi]
      have h0 : i ≠ ports 0 := fun h => hi ⟨0,h.symm⟩
      have h1' : i ≠ ports 1 := fun h => hi ⟨1,h.symm⟩
      have h2' : i ≠ ports 2 := fun h => hi ⟨2,h.symm⟩
      simp [parsedStacks,h0,h1',h2']

abbrev emit (ports : Fin 6 ↪ Fin 128) : Cmd 16 128 :=
  .call (ProgramLinking.liftProgram RawEmitter.emitRawTermProgram registers ports)

def emittedStacks (ports : Fin 6 ↪ Fin 128) (key coefficient : List Bool)
    (stk : Fin 128 → List Bool) : Fin 128 → List Bool :=
  Function.update (Function.update (Function.update stk (ports 0) []) (ports 1) [])
    (ports 3) (true :: (Encoding.frame (SubexpArgumentProgram.recordBody key coefficient) ++
      stk (ports 3)))

theorem emit_eval (ports : Fin 6 ↪ Fin 128) (d : Data) (key coefficient : List Bool)
    (hin : d.stacks (ports 0) = coefficient) (hkey : d.stacks (ports 1) = key.reverse)
    (h4 : d.stacks (ports 4) = []) (h5 : d.stacks (ports 5) = []) :
    ∃ e : Data, Eval (emit ports) (37*coefficient.length+21*key.length+57) d e ∧
      e.stacks = emittedStacks ports key coefficient d.stacks := by
  let rs : Fin 5 → Bool := fun i => d.regs (registers i)
  let a := recordState rs coefficient key.reverse (d.stacks (ports 2)) (d.stacks (ports 3)) [] []
  let b := recordState (SubexpArgumentProgram.finishedRegs rs) [] [] (d.stacks (ports 2))
    (true :: (Encoding.frame (SubexpArgumentProgram.recordBody key coefficient) ++ d.stacks (ports 3))) [] []
  have ha : embedState registers ports d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ registers.injective ports.injective
    · intro i; rfl
    · intros; rfl
    · intro i
      fin_cases i <;> first | exact hin | exact hkey | exact h4 | exact h5 | rfl
    · intros; rfl
  let e := embedState registers ports d b
  have ht := eval_call_lifted RawEmitter.emitRawTermProgram registers ports d
    registers.injective ports.injective
    (RawEmitter.emitRawTerm_trace key coefficient (d.stacks (ports 2)) (d.stacks (ports 3)) rs)
  change Eval (emit ports) _ (embedState registers ports d a) e at ht
  refine ⟨e, ?_, ?_⟩
  · simpa only [ha] using ht
  · funext i
    have heq (j k : Fin 6) : ports j = ports k ↔ j = k := ports.injective.eq_iff
    by_cases hi : ∃ j, ports j = i
    · obtain ⟨j, rfl⟩ := hi
      change (embedState registers ports d b).stacks (ports j) = _
      rw [embedState_stack _ _ _ _ ports.injective]
      fin_cases j <;> simp [b, storage, emittedStacks, heq, h4, h5]
    · change (embedState registers ports d b).stacks i = _
      rw [embedState_stack_frame _ _ _ _ _ hi]
      have h0 : i ≠ ports 0 := fun h => hi ⟨0,h.symm⟩
      have h1 : i ≠ ports 1 := fun h => hi ⟨1,h.symm⟩
      have h3 : i ≠ ports 3 := fun h => hi ⟨3,h.symm⟩
      simp [emittedStacks,h0,h1,h3]

end SubexponentialSAT.SubexpDenseRecordCalls

end OAI.Algorithms
