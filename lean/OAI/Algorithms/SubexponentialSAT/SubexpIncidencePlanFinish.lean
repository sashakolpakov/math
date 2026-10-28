import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpIncidencePlanPrimitives
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCopyProgram
import OAI.Algorithms.SubexponentialSAT.ArrayPrograms

namespace OAI.Algorithms

/-! Physical head and padding-offset preparation for an incidence read plan. -/
namespace SubexponentialSAT.SubexpIncidencePlanFinish


open BitProgram StructuredCalls

abbrev Data := State 10 16
abbrev Code := Cmd 10 16
abbrev unary (n : ℕ) := List.replicate n true

def copy (src dst : Fin 16) : Code := .call (StackRoutines.copyProgram src dst 3 0 1)
abbrev copied (src dst : Fin 16) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩
theorem copy_eval (src dst : Fin 16) (d : Data)
    (hsd : src ≠ dst) (hs : src ≠ 3) (hd : (3 : Fin 16) ≠ dst) (ht : d.stacks 3 = []) :
    Eval (copy src dst) (7*(d.stacks src).length+5) d (copied src dst d) :=
  .call _ (ListRegisterProgram.copy_run src dst 3 0 1 hsd hs hd (by decide) d.regs d.stacks ht)

def transfer (src dst : Fin 16) : Code := .call (StackRoutines.transferProgram src dst 0 1)
abbrev transferred (src dst : Fin 16) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩
theorem transfer_eval (src dst : Fin 16) (d : Data) (hsd : src ≠ dst) :
    Eval (transfer src dst) (3*(d.stacks src).length+3) d (transferred src dst d) :=
  .call _ (ListRegisterProgram.transfer_run src dst 0 1 hsd (by decide) d.regs d.stacks)

def pop (src : Fin 16) : Code := .base (.atom (.pop src 0 1))
abbrev popped (src : Fin 16) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 (d.stacks src).head?, Function.update d.stacks src (d.stacks src).tail⟩
theorem pop_eval (src : Fin 16) (d : Data) : Eval (pop src) 1 d (popped src d) :=
  .base (.atom _ _)

def set (i : Fin 10) (b : Bool) : Code := .base (.atom (.set i b))
def setState (i : Fin 10) (b : Bool) (d : Data) : Data := ⟨Function.update d.regs i b,d.stacks⟩
theorem set_eval (i : Fin 10) (b : Bool) (d : Data) : Eval (set i b) 1 d (setState i b d) :=
  .base (.atom _ _)

def pushFalse (dst : Fin 16) : Code := .seq (set 0 false) (.base (.atom (.push dst 0)))
abbrev pushedFalse (dst : Fin 16) (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks dst (false::d.stacks dst)⟩
theorem pushFalse_eval (dst : Fin 16) (d : Data) :
    Eval (pushFalse dst) 2 d (pushedFalse dst d) := by
  have h := (set_eval 0 false d).seq (Eval.base (StructuredProgram.Eval.atom (.push dst 0) _))
  simpa [pushFalse, setState, pushedFalse, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h

def emitRegisters : Fin 3 → Fin 10 := ![0,1,4]
def emitStacks : Fin 4 → Fin 16 := ![6,3,7,1]
theorem emitRegisters_injective : Function.Injective emitRegisters := by decide
theorem emitStacks_injective : Function.Injective emitStacks := by decide
def emit : Code := .call (ProgramLinking.liftProgram
  SubexpNormalizeProgram.emitIfSelectedProgram emitRegisters emitStacks)
abbrev emitted (bits : List Bool) (d : Data) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 true) 4 false,
    Function.update (Function.update d.stacks 1 []) 7 (true::Encoding.frame bits++d.stacks 7)⟩

theorem emit_eval (bits : List Bool) (d : Data) (hp : d.stacks 1 = bits.reverse)
    (hf : d.regs 4 = true) : Eval emit (5*bits.length+12) d (emitted bits d) := by
  let a := SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) true
    (d.stacks 6) (d.stacks 3) (d.stacks 7) bits.reverse
  let b := SubexpNormalizeProgram.filterState false true false
    (d.stacks 6) (d.stacks 3) (true::Encoding.frame bits++d.stacks 7) []
  have ha : embedState emitRegisters emitStacks d a = d := by
    apply embedState_eq_of_ports emitRegisters emitStacks d d a emitRegisters_injective emitStacks_injective
    · intro i; fin_cases i <;> simp [a,emitRegisters,SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.triple,hf]
    · intros; rfl
    · intro i; fin_cases i <;> simp [a,emitStacks,SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple,hp]
    · intros; rfl
  have hb : embedState emitRegisters emitStacks d b = emitted bits d := by
    apply embedState_eq_of_ports emitRegisters emitStacks d (emitted bits d) b
      emitRegisters_injective emitStacks_injective
    · intro i; fin_cases i <;> simp [b,emitRegisters,SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.triple]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1,h.symm⟩
      have h4 : i ≠ 4 := fun h => hi ⟨2,h.symm⟩
      simp [h0,h1,h4]
    · intro i; fin_cases i <;> simp [b,emitStacks,SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple]
    · intro i hi
      have h1 : i ≠ 1 := fun h => hi ⟨3,h.symm⟩
      have h7 : i ≠ 7 := fun h => hi ⟨2,h.symm⟩
      simp [h1,h7]
  have h := eval_call_lifted SubexpNormalizeProgram.emitIfSelectedProgram emitRegisters emitStacks d
    emitRegisters_injective emitStacks_injective
    (SubexpNormalizeProgram.emitIfSelected_trace true bits
      (d.stacks 6) (d.stacks 3) (d.stacks 7) (d.regs 0) (d.regs 1))
  change Eval emit _ (embedState emitRegisters emitStacks d a) (embedState emitRegisters emitStacks d b) at h
  simpa [ha,hb,SubexpNormalizeProgram.emitIfSelectedSteps] using h

def state (regs : Fin 10 → Bool) (v E degree D Δ : ℕ) (out : List Bool)
    (index vertex fuel counter : List Bool := []) : Data :=
  ⟨regs, ![[], index, (Encoding.encodeNat v).reverse, [], [], unary E, [], out,
    [], unary degree, unary D, unary Δ, [], vertex, fuel, counter]⟩

def header : Code := .seq (copy 2 13) (.seq (pop 13) (.seq (copy 13 1)
  (.seq (copy 5 1) (.seq (transfer 7 12) (.seq (pushFalse 7)
    (.seq (set 4 true) (.seq emit (transfer 12 7))))))))

def headerWord (E v : ℕ) (out : List Bool) : List Bool :=
  out ++ (true::Encoding.frame (unary (E+v)) ++ [false])

theorem header_eval (regs : Fin 10 → Bool) (v E degree D Δ : ℕ) (out : List Bool) :
    ∃ rf, Eval header (19*v+12*E+6*out.length+44)
      (state regs v E degree D Δ out)
      (state rf v E degree D Δ (headerWord E v out) [] (unary v)) := by
  let a := state regs v E degree D Δ out
  let a1 := copied 2 13 a
  let a2 := popped 13 a1
  let a3 := copied 13 1 a2
  let a4 := copied 5 1 a3
  let a5 := transferred 7 12 a4
  let a6 := pushedFalse 7 a5
  let a7 := setState 4 true a6
  let a8 := emitted (unary (E+v)) a7
  let a9 := transferred 12 7 a8
  have h1 := copy_eval 2 13 a (by decide) (by decide) (by decide) rfl
  have h2 := pop_eval 13 a1
  have h3 := copy_eval 13 1 a2 (by decide) (by decide) (by decide)
    (by simp [a2,a1,StackRoutines.copyStacks,a,state])
  have h4 := copy_eval 5 1 a3 (by decide) (by decide) (by decide)
    (by simp [a3,StackRoutines.copyStacks,a2,a1,a,state])
  have h5 := transfer_eval 7 12 a4 (by decide)
  have h6 := pushFalse_eval 7 a5
  have h7 := set_eval 4 true a6
  have h8 := emit_eval (unary (E+v)) a7
    (by simp [a7,setState,a6,a5,StackRoutines.transferStacks,
      a4,StackRoutines.copyStacks,a3,a2,a1,a,state,Encoding.encodeNat
      ]) (by simp [a7,setState])
  have h9 := transfer_eval 12 7 a8 (by decide)
  have he : a9 = state a9.regs v E degree D Δ (headerWord E v out) [] (unary v) := by
    apply congrArg (StructuredProgram.State.mk a9.regs)
    funext i
    fin_cases i <;> simp [StackRoutines.transferStacks,a8,a7,setState,
      a6,a5,a4,StackRoutines.copyStacks,a3,a2,a1,a,state,
      Encoding.encodeNat,headerWord]
  have h := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq h9)))))))
  change Eval header _ a a9 at h
  rw [he] at h
  refine ⟨a9.regs, ?_⟩
  convert h using 1
  simp [a1,a2,a3,a4,a5,a6,a7,a8,a,state,
    setState,StackRoutines.copyStacks,StackRoutines.transferStacks,Encoding.encodeNat]
  omega

def subtract : Code := .call (ArrayPrograms.countedSkipProgram 15 14 3 0 1)
abbrev subtracted (rest : List Bool) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, ArrayPrograms.countedSkipStacks 15 14 rest d.stacks⟩
theorem subtract_eval (d : Data) (degree Δ : ℕ) (hd : degree ≤ Δ)
    (h15 : d.stacks 15 = unary degree) (h14 : d.stacks 14 = unary Δ) (h3 : d.stacks 3 = []) :
    Eval subtract (6*degree+5) d (subtracted (unary (Δ-degree)) d) := by
  have hs : d.stacks 14 = unary degree ++ unary (Δ-degree) := by
    rw [h14, ← List.replicate_add, Nat.add_sub_of_le hd]
  have h := ArrayPrograms.countedSkipProgram_trace (15 : Fin 16) 14 3 (0 : Fin 10) 1
    (by decide) (by decide) (by decide) (by decide) (unary degree) (unary (Δ-degree))
    (unary degree) d.regs d.stacks hs h15 rfl h3
  have ht := StackRoutines.halt_after_trace _ h 6 rfl rfl
  exact .call _ (by simpa [subtracted,ArrayPrograms.countedSkipResult,Nat.add_assoc] using ht)

def repeatRegisters : Fin 3 → Fin 10 := ![0,1,4]
def repeatStacks : Fin 4 → Fin 16 := ![11,1,3,15]
theorem repeatRegisters_injective : Function.Injective repeatRegisters := by decide
theorem repeatStacks_injective : Function.Injective repeatStacks := by decide
def repeatCall : Code := .call (ProgramLinking.liftProgram
  Subexp.BlockCopyProgram.program repeatRegisters repeatStacks)
def repeatCopies : Code := .seq (set 0 false) (.seq (set 1 false) (.seq (set 4 false) repeatCall))
abbrev repeated (n : ℕ) (bits : List Bool) (d : Data) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 false) 4 false,
    Function.update (Function.update d.stacks 15 []) 1
      (Subexp.BlockCopyProgram.copies n bits ++ d.stacks 1)⟩

theorem repeat_eval (d : Data) (n : ℕ) (bits : List Bool)
    (hb : d.stacks 11 = bits) (hn : d.stacks 15 = unary n) (ht : d.stacks 3 = []) :
    Eval repeatCopies (n*(7*bits.length+7)+6) d (repeated n bits d) := by
  let d1 := setState 0 false d
  let d2 := setState 1 false d1
  let d3 := setState 4 false d2
  let a := Subexp.BlockCopyProgram.initialState n bits (d.stacks 1)
  let b := Subexp.BlockCopyProgram.data false false bits
    (Subexp.BlockCopyProgram.copies n bits ++ d.stacks 1) []
  have ha : embedState repeatRegisters repeatStacks d3 a = d3 := by
    apply embedState_eq_of_ports repeatRegisters repeatStacks d3 d3 a
      repeatRegisters_injective repeatStacks_injective
    · intro i; fin_cases i <;> simp [a,Subexp.BlockCopyProgram.initialState,
        Subexp.BlockCopyProgram.data,repeatRegisters,d3,d2,d1,setState]
    · intros; rfl
    · intro i; fin_cases i <;> simp [a,Subexp.BlockCopyProgram.initialState,
        Subexp.BlockCopyProgram.data,repeatStacks,d3,d2,d1,setState,hb,hn,ht]
    · intros; rfl
  have he : embedState repeatRegisters repeatStacks d3 b = repeated n bits d := by
    apply embedState_eq_of_ports repeatRegisters repeatStacks d3 (repeated n bits d) b
      repeatRegisters_injective repeatStacks_injective
    · intro i; fin_cases i <;> simp [b,Subexp.BlockCopyProgram.data,repeatRegisters]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0,h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1,h.symm⟩
      have h4 : i ≠ 4 := fun h => hi ⟨2,h.symm⟩
      simp [d3,d2,d1,setState,h0,h1,h4]
    · intro i; fin_cases i <;> simp [b,Subexp.BlockCopyProgram.data,repeatStacks,hb,ht]
    · intro i hi
      have h1 : i ≠ 1 := fun h => hi ⟨1,h.symm⟩
      have h15 : i ≠ 15 := fun h => hi ⟨3,h.symm⟩
      simp [d3,d2,d1,setState,h1,h15]
  have h := eval_call_lifted Subexp.BlockCopyProgram.program repeatRegisters repeatStacks d3
    repeatRegisters_injective repeatStacks_injective
    (Subexp.BlockCopyProgram.program_trace n bits (d.stacks 1))
  change Eval repeatCall _ (embedState repeatRegisters repeatStacks d3 a)
    (embedState repeatRegisters repeatStacks d3 b) at h
  rw [ha,he] at h
  have hall := (set_eval 0 false d).seq ((set_eval 1 false d1).seq ((set_eval 4 false d2).seq h))
  convert hall using 1
  all_goals first | rfl | omega

theorem copies_unary (n m : ℕ) : Subexp.BlockCopyProgram.copies n (unary m) = unary (n*m) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Subexp.BlockCopyProgram.copies_succ,ih,← List.replicate_add]; congr 1; ring

def paddingStart (v E degree D Δ : ℕ) := E+D+v*Δ+degree
def prepare : Code := .seq (copy 11 14) (.seq (copy 9 15) (.seq subtract
  (.seq (copy 10 1) (.seq (copy 5 1) (.seq (copy 9 1) (.seq (copy 13 15) repeatCopies))))))

theorem prepare_eval (regs : Fin 10 → Bool) (v E degree D Δ : ℕ) (out : List Bool)
    (hd : degree ≤ Δ) :
    ∃ rf, Eval prepare (7*Δ+20*degree+7*D+7*E+14*v+7*v*Δ+41)
      (state regs v E degree D Δ out [] (unary v))
      (state rf v E degree D Δ out (unary (paddingStart v E degree D Δ)) (unary v)
        (unary (Δ-degree))) := by
  let a := state regs v E degree D Δ out [] (unary v)
  let a1 := copied 11 14 a
  let a2 := copied 9 15 a1
  let a3 := subtracted (unary (Δ-degree)) a2
  let a4 := copied 10 1 a3
  let a5 := copied 5 1 a4
  let a6 := copied 9 1 a5
  let a7 := copied 13 15 a6
  let a8 := repeated v (unary Δ) a7
  have h1 := copy_eval 11 14 a (by decide) (by decide) (by decide) rfl
  have h2 := copy_eval 9 15 a1 (by decide) (by decide) (by decide)
    (by simp [a1,StackRoutines.copyStacks,a,state])
  have h3 := subtract_eval a2 degree Δ hd
    (by simp [a2,a1,StackRoutines.copyStacks,a,state])
    (by simp [a2,a1,StackRoutines.copyStacks,a,state])
    (by simp [a2,a1,StackRoutines.copyStacks,a,state])
  have h4 := copy_eval 10 1 a3 (by decide) (by decide) (by decide)
    (by simp [a3,ArrayPrograms.countedSkipStacks,a2,a1,StackRoutines.copyStacks,a,state])
  have h5 := copy_eval 5 1 a4 (by decide) (by decide) (by decide)
    (by simp [a4,StackRoutines.copyStacks,a3,ArrayPrograms.countedSkipStacks,a2,a1,a,state])
  have h6 := copy_eval 9 1 a5 (by decide) (by decide) (by decide)
    (by simp [a5,a4,StackRoutines.copyStacks,a3,ArrayPrograms.countedSkipStacks,a2,a1,a,state])
  have h7 := copy_eval 13 15 a6 (by decide) (by decide) (by decide)
    (by simp [a6,a5,a4,StackRoutines.copyStacks,a3,ArrayPrograms.countedSkipStacks,a2,a1,a,state])
  have h8 := repeat_eval a7 v (unary Δ)
    (by simp [a7,a6,a5,a4,StackRoutines.copyStacks,a3,ArrayPrograms.countedSkipStacks,a2,a1,a,state])
    (by simp [a7,a6,a5,a4,StackRoutines.copyStacks,a3,ArrayPrograms.countedSkipStacks,a2,a1,a,state])
    (by simp [a7,a6,a5,a4,StackRoutines.copyStacks,a3,ArrayPrograms.countedSkipStacks,a2,a1,a,state])
  have he : a8 = state a8.regs v E degree D Δ out (unary (paddingStart v E degree D Δ))
      (unary v) (unary (Δ-degree)) := by
    apply congrArg (StructuredProgram.State.mk a8.regs)
    funext i
    fin_cases i <;> simp [copies_unary,a7,a6,a5,a4,StackRoutines.copyStacks,
      a3,ArrayPrograms.countedSkipStacks,a2,a1,a,state,paddingStart,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  have h := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq h8))))))
  change Eval prepare _ a a8 at h
  rw [he] at h
  refine ⟨a8.regs,?_⟩
  convert h using 1
  simp [a6,a5,a4,StackRoutines.copyStacks,a3,ArrayPrograms.countedSkipStacks,a2,a1,a,state]
  ring

end SubexponentialSAT.SubexpIncidencePlanFinish

end OAI.Algorithms
