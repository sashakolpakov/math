import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticMarshal
import OAI.Algorithms.SubexponentialSAT.SubexpRawArgumentService
import OAI.Algorithms.SubexponentialSAT.SubexpScalarLiteralProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Actual constant-quartic padding and raw singleton emission after a
weight word has been computed. This stage uses no scalar arithmetic oracle. -/

namespace SubexponentialSAT.SubexpWeightLiteralProgram

open BitProgram StructuredCalls

abbrev Word := List Bool
abbrev Data := State 8 24
abbrev Code := Cmd 8 24

def smallRegs : Fin 3 → Fin 8 := Fin.castAdd 5
def rawRegs : Fin 5 → Fin 8 := Fin.castAdd 3
def marshalPorts : Fin 5 → Fin 24 := ![0,12,1,2,3]
def rawPorts : Fin 10 → Fin 24 := ![0,1,2,15,3,4,6,7,8,9]

theorem smallRegs_injective : Function.Injective smallRegs := Fin.castAdd_injective 3 5
theorem rawRegs_injective : Function.Injective rawRegs := Fin.castAdd_injective 5 3
theorem marshalPorts_injective : Function.Injective marshalPorts := by decide
theorem rawPorts_injective : Function.Injective rawPorts := by decide

def state (regs : Fin 8 → Bool) (word modulus records shape : Word)
    (D I : ℕ) (out : Word) : Data :=
  ⟨regs,fun i => match i.val with
    | 0 => word | 5 => modulus | 11 => records | 12 => shape
    | 13 => List.replicate D true | 14 => List.replicate I true
    | 15 => out | _ => []⟩

def marshal : Code :=
  .call (ProgramLinking.liftProgram SubexpQuarticMarshal.program smallRegs marshalPorts)

def copy (src dst : Fin 24) : Code :=
  .call (StackRoutines.copyProgram src dst 16 (0 : Fin 8) 1)

def setup : Code := .base (.seq (.atom (.set 2 false))
  (.seq (.atom (.set 3 false)) (.seq (.atom (.set 0 false)) (.atom (.push 15 0)))))

def prepare : Code := .seq setup (.seq (copy 13 2) (copy 14 6))

def emit : Code :=
  .call (ProgramLinking.liftProgram SubexpRawArgumentService.program rawRegs rawPorts)

def readyRegs (r : Fin 8 → Bool) : Fin 8 → Bool :=
  readRegs (Function.update (Function.update (Function.update r 2 false) 3 false) 0 false) 0 1 none

def ready (r : Fin 8 → Bool) (word modulus records shape : Word) (D I : ℕ) : Data :=
  ⟨readyRegs r,fun i => match i.val with
    | 0 => word | 2 => List.replicate D true | 5 => modulus
    | 6 => List.replicate I true | 11 => records | 12 => shape
    | 13 => List.replicate D true | 14 => List.replicate I true
    | 15 => [false] | _ => []⟩

theorem marshal_eval (r : Fin 8 → Bool) (word modulus records shape : Word) (D I : ℕ) :
    ∃ rf, Eval marshal (6*word.length+12*shape.length+15)
      (state r word modulus records shape D I [])
      (state rf (SubexpQuarticMarshal.marshalBits word shape) modulus records shape D I []) := by
  obtain ⟨rr,ht⟩ := SubexpQuarticMarshal.run (r ∘ smallRegs) word shape
  let d := state r word modulus records shape D I []
  let rf := Function.extend smallRegs rr r
  have h := eval_call_lifted SubexpQuarticMarshal.program smallRegs marshalPorts d
    smallRegs_injective marshalPorts_injective
    (a := ⟨r ∘ smallRegs,SubexpQuarticMarshal.stackState word shape [] [] []⟩)
    (b := ⟨rr,SubexpQuarticMarshal.stackState
      (SubexpQuarticMarshal.marshalBits word shape) shape [] [] []⟩) ht
  have hstart : embedState smallRegs marshalPorts d
      ⟨r ∘ smallRegs,SubexpQuarticMarshal.stackState word shape [] [] []⟩ = d := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective marshalPorts_injective
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hend : embedState smallRegs marshalPorts d
      ⟨rr,SubexpQuarticMarshal.stackState (SubexpQuarticMarshal.marshalBits word shape) shape [] [] []⟩ =
      state rf (SubexpQuarticMarshal.marshalBits word shape) modulus records shape D I [] := by
    apply embedState_eq_of_ports _ _ _ _ _ smallRegs_injective marshalPorts_injective
    · intro i
      exact Function.Injective.extend_apply smallRegs_injective rr r i
    · intro i hi
      exact Function.extend_apply' _ _ _ hi
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
      fin_cases i <;> first | contradiction | rfl
  rw [hstart,hend] at h
  exact ⟨rf,h⟩

theorem prepare_eval (r : Fin 8 → Bool) (word modulus records shape : Word) (D I : ℕ) :
    Eval prepare (7*D+7*I+14) (state r word modulus records shape D I [])
      (ready r word modulus records shape D I) := by
  let d := state r word modulus records shape D I []
  let r0 := Function.update (Function.update (Function.update r 2 false) 3 false) 0 false
  let a : Data := ⟨r0,Function.update d.stacks 15 [false]⟩
  have hi : Eval setup 4 d a := by
    have h := (StructuredProgram.Eval.atom (.set (2 : Fin 8) false) d).seq
      ((StructuredProgram.Eval.atom (.set (3 : Fin 8) false) _).seq
        ((StructuredProgram.Eval.atom (.set (0 : Fin 8) false) _).seq
          (StructuredProgram.Eval.atom (.push (15 : Fin 24) 0) _)))
    exact .base (by simpa [a,r0,d,state,StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,
      StructuredProgram.State.withPC,execInstr] using h)
  let b : Data := ⟨readRegs r0 0 1 none,StackRoutines.copyStacks 13 2 a.stacks⟩
  have h1 : Eval (copy 13 2) (7*D+5) a b := by
    apply Eval.call
    have hlen : (a.stacks 13).length = D := by simp [a,d,state]
    simpa only [hlen] using ListRegisterProgram.copy_run 13 2 16 0 1
      (by decide) (by decide) (by decide) (by decide) a.regs a.stacks rfl
  have h2 := ListRegisterProgram.copy_run (14 : Fin 24) 6 16 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) b.regs b.stacks (by rfl)
  have he : (⟨readRegs b.regs 0 1 none,StackRoutines.copyStacks (14 : Fin 24) 6 b.stacks⟩ : Data) =
      ready r word modulus records shape D I := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [readyRegs, b, r0, readRegs]
    · funext i; fin_cases i <;> simp [b, a, d, state, StackRoutines.copyStacks]
  have hh : Eval (copy 14 6) (7*I+5) b (ready r word modulus records shape D I) := by
    have h : Eval (copy 14 6) _ b
        ⟨readRegs b.regs 0 1 none,StackRoutines.copyStacks (14 : Fin 24) 6 b.stacks⟩ := .call _ h2
    rw [he] at h
    simpa [b,a,d,state,StackRoutines.copyStacks] using h
  have h := Eval.seq hi (Eval.seq h1 hh)
  have hcost : 4 + ((7 * D + 5) + (7 * I + 5)) = 7 * D + 7 * I + 14 := by
    omega
  rw [hcost] at h
  simpa only [prepare, d] using h

theorem emit_eval (r : Fin 8 → Bool) (word modulus records shape : Word) (D : ℕ) :
    ∃ rf, Eval emit
      (SubexpRawArgumentService.cost D 0 0 (SubexpSymbolicCost.indexBits D) false false word + 1)
      (ready r word modulus records shape D (SubexpSymbolicCost.indexBits D))
      (state rf [] modulus records shape D (SubexpSymbolicCost.indexBits D)
        (SubexpScalarLiteralProgram.rawLiteral D word)) := by
  let d := ready r word modulus records shape D (SubexpSymbolicCost.indexBits D)
  let rr := readyRegs r ∘ rawRegs
  let rf := Function.extend rawRegs (SubexpArgumentProgram.finishedRegs rr) d.regs
  have ht := SubexpRawArgumentService.program_trace D 0 0 (SubexpSymbolicCost.indexBits D)
    rr word [false] []
  have hm : rr 2 = false := by simp [rr,readyRegs,rawRegs,readRegs]
  have hu : rr 3 = false := by simp [rr,readyRegs,rawRegs,readRegs]
  rw [hm,hu,SubexpArgumentKeyEmitter.paddedKey_constant] at ht
  change Trace _ _ _ ((SubexpRawArgumentService.state
    (SubexpArgumentProgram.finishedRegs rr) [] [] []
    (SubexpScalarLiteralProgram.rawLiteral D word) [] [] [] []).withPC none) at ht
  have h := eval_call_lifted SubexpRawArgumentService.program rawRegs rawPorts d
    rawRegs_injective rawPorts_injective ht
  have hstart : embedState rawRegs rawPorts d
      (SubexpRawArgumentService.state rr word [] (List.replicate D true) [false]
        [] [] (List.replicate (SubexpSymbolicCost.indexBits D) true) []) = d := by
    apply embedState_eq_of_ports _ _ _ _ _ rawRegs_injective rawPorts_injective
    · intro i; rfl
    · intros; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hend : embedState rawRegs rawPorts d
      (SubexpRawArgumentService.state (SubexpArgumentProgram.finishedRegs rr) [] [] []
        (SubexpScalarLiteralProgram.rawLiteral D word) [] [] [] []) =
      state rf [] modulus records shape D (SubexpSymbolicCost.indexBits D)
        (SubexpScalarLiteralProgram.rawLiteral D word) := by
    apply embedState_eq_of_ports _ _ _ _ _ rawRegs_injective rawPorts_injective
    · intro i
      exact Function.Injective.extend_apply rawRegs_injective _ d.regs i
    · intro i hi
      exact Function.extend_apply' _ _ _ hi
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
      have h2 : i ≠ 2 := fun h => hi ⟨2,h.symm⟩
      have h6 : i ≠ 6 := fun h => hi ⟨6,h.symm⟩
      have h15 : i ≠ 15 := fun h => hi ⟨3,h.symm⟩
      fin_cases i
      · exact (h0 rfl).elim
      · rfl
      · exact (h2 rfl).elim
      · rfl
      · rfl
      · rfl
      · exact (h6 rfl).elim
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · exact (h15 rfl).elim
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
  simp only [List.replicate_zero] at h
  rw [hstart,hend] at h
  exact ⟨rf,h⟩

/-- This bound includes the actual weight run, padding, master copies, key
generation, and raw coefficient record emission. -/
def overhead (D B : ℕ) : ℕ :=
  18*B+15 + (7*D+7*SubexpSymbolicCost.indexBits D+14) +
    (SubexpArgumentKeyEmitter.rawCost D 0 0 false false +
      4*(SubexpSymbolicCost.indexBits D -
        (SubexpArgumentKeyEmitter.rawKey D 0 0 false false).length)+3 +
      (37*(4*B)+21*(SubexpArgumentKeyEmitter.paddedKey D 0 0
        (SubexpSymbolicCost.indexBits D) false false).length+57)+1) + 1

theorem rawLiteral_length (D : ℕ) (coefficient : Word) :
    (SubexpScalarLiteralProgram.rawLiteral D coefficient).length =
      4*SubexpSymbolicCost.indexBits D + 4*coefficient.length + 7 := by
  have hk : (SubexpArgumentKeyEmitter.rawKey D 0 0 false false).length = D+2 := by
    simp [SubexpArgumentKeyEmitter.rawKey,SubexpArgumentKeyEmitter.markBits,
      SubexpArgumentKeyEmitter.uBits]
  have hw : D+2 ≤ SubexpSymbolicCost.indexBits D := by
    unfold SubexpSymbolicCost.indexBits
    nlinarith
  have hp : (SubexpSymbolicCost.fixedKey
      (SubexpArgumentCode.constantIndex D 0 0)).length = SubexpSymbolicCost.indexBits D := by
    have hc : SubexpArgumentKeyEmitter.paddedKey D 0 0
        (SubexpSymbolicCost.indexBits D) false false =
        SubexpSymbolicCost.fixedKey (SubexpArgumentCode.constantIndex D 0 0) := by
      simpa only [Bool.false_eq_true,ite_false] using
        SubexpArgumentKeyEmitter.paddedKey_constant D 0 false
    rw [←hc]
    simp only [SubexpArgumentKeyEmitter.paddedKey,List.length_append,List.length_replicate,hk]
    exact Nat.add_sub_of_le hw
  simp [SubexpScalarLiteralProgram.rawLiteral, Encoding.encodeList,
    SubexpArgumentProgram.recordBody, hp, Nat.mul_add]
  omega

theorem overhead_le (D B : ℕ) :
    overhead D B ≤ 166*B+12*D+32*SubexpSymbolicCost.indexBits D+105 := by
  have hk : (SubexpArgumentKeyEmitter.rawKey D 0 0 false false).length = D+2 := by
    simp [SubexpArgumentKeyEmitter.rawKey,SubexpArgumentKeyEmitter.markBits,
      SubexpArgumentKeyEmitter.uBits]
  have hw : (SubexpArgumentKeyEmitter.rawKey D 0 0 false false).length ≤
      SubexpSymbolicCost.indexBits D := by
    rw [hk]
    unfold SubexpSymbolicCost.indexBits
    nlinarith
  have hp : (SubexpArgumentKeyEmitter.paddedKey D 0 0
      (SubexpSymbolicCost.indexBits D) false false).length =
      SubexpSymbolicCost.indexBits D := by
    simp only [SubexpArgumentKeyEmitter.paddedKey,List.length_append,List.length_replicate]
    exact Nat.add_sub_of_le hw
  have hc := SubexpArgumentKeyEmitter.rawCost_le D 0 0 false false
  rw [hk] at hc
  unfold overhead
  rw [hp]
  omega


end SubexponentialSAT.SubexpWeightLiteralProgram

end OAI.Algorithms
