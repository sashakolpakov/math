import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.TypeBitFilter
import OAI.Algorithms.SubexponentialSAT.Subexp.TypeIndexProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.TypeEnumeration

namespace OAI.Algorithms

/-! Repeatable physical Side/Joint filters. Metadata occupies ports 11--15;
all work ports are cleared, and both metadata and saved source are preserved. -/

namespace SubexponentialSAT.Subexp.TypeFiberProgram

open BitProgram StructuredCalls TupleProgram
open BlockSearchPreparation (restrictState lifted_call)

abbrev Data := State 8 16

structure Context where
  r : ℕ
  t : ℕ
  g : ℕ
  width : ℕ
  i : ℕ

def Context.offset (ctx : Context) (joint : Bool) : ℕ :=
  if joint then TypeEnumeration.slotIndex ctx.r ctx.width ctx.t ctx.g ctx.i
  else TypeEnumeration.headIndex ctx.r ctx.t ctx.g

def state (ctx : Context) (regs : Fin 8 → Bool) (source index output : List Bool) : Data :=
  ⟨regs,fun j => if j = 0 then source else if j = 1 then index else if j = 10 then output
    else if j = 11 then TypeIndexProgram.unary ctx.r
    else if j = 12 then TypeIndexProgram.unary ctx.t
    else if j = 13 then TypeIndexProgram.unary ctx.g
    else if j = 14 then TypeIndexProgram.unary ctx.width
    else if j = 15 then TypeIndexProgram.unary ctx.i else []⟩

def inputState (ctx : Context) (words : Records) (regs : Fin 8 → Bool) : Data :=
  state ctx regs (ProgramEncoding.encodeRecords words) [] []

def resultWords (joint : Bool) (ctx : Context) (words : Records) : Records :=
  words.filter (TypeBitFilter.test (!joint) (ctx.offset joint))

def outputState (joint : Bool) (ctx : Context) (words : Records) (regs : Fin 8 → Bool) : Data :=
  state ctx regs (ProgramEncoding.encodeRecords words) []
    (ProgramEncoding.encodeRecords (resultWords joint ctx words))

abbrev prepare (joint : Bool) : Cmd 8 16 :=
  if joint then TypeIndexProgram.jointCommand else TypeIndexProgram.headCommand

def prepareCost (joint : Bool) (ctx : Context) : ℕ :=
  if joint then TypeIndexProgram.jointCost ctx.r ctx.width ctx.t ctx.g ctx.i
  else TypeIndexProgram.headCost ctx.r ctx.t ctx.g

theorem prepare_eval (joint : Bool) (ctx : Context) (source : List Bool) (regs : Fin 8 → Bool) :
    ∃ nextRegs, Eval (prepare joint) (prepareCost joint ctx) (state ctx regs source [] [])
      (state ctx nextRegs source (TypeIndexProgram.unary (ctx.offset joint)) []) := by
  let a := state ctx regs source [] []
  cases joint with
  | false =>
      have ht := TypeIndexProgram.head_eval ctx.r ctx.t ctx.g a rfl rfl rfl rfl rfl rfl
      let b := TypeIndexProgram.headResult ctx.r ctx.t ctx.g a
      have hb : b = state ctx b.regs source (TypeIndexProgram.unary (ctx.offset false)) [] := by
        apply congrArg₂ StructuredProgram.State.mk rfl
        funext j
        by_cases h1 : j = 1
        · subst j
          change (TypeIndexProgram.headResult ctx.r ctx.t ctx.g a).stacks 1 =
            TypeIndexProgram.unary (ctx.t * ctx.r + ctx.g)
          simpa only [b, Context.offset, TypeEnumeration.headIndex, Bool.false_eq] using
            TypeIndexProgram.headResult_output ctx.r ctx.t ctx.g a rfl rfl rfl
        · by_cases h7 : j = 7
          · subst j; simp []
          · change (TypeIndexProgram.headResult ctx.r ctx.t ctx.g a).stacks j = _
            rw [TypeIndexProgram.headResult_frame ctx.r ctx.t ctx.g a j h1 h7]
            simp only [a,state,h1,ite_false]
      change Eval TypeIndexProgram.headCommand (TypeIndexProgram.headCost ctx.r ctx.t ctx.g) a b at ht
      rw [hb] at ht
      exact ⟨b.regs,ht⟩
  | true =>
      have ht := TypeIndexProgram.joint_eval ctx.r ctx.width ctx.t ctx.g ctx.i a
        rfl rfl rfl rfl rfl rfl rfl rfl
      let b := TypeIndexProgram.jointResult ctx.r ctx.t ctx.g ctx.i a
      have hb : b = state ctx b.regs source (TypeIndexProgram.unary (ctx.offset true)) [] := by
        apply congrArg₂ StructuredProgram.State.mk rfl
        funext j
        by_cases h1 : j = 1
        · subst j
          change (TypeIndexProgram.jointResult ctx.r ctx.t ctx.g ctx.i a).stacks 1 =
            TypeIndexProgram.unary ((ctx.i + 1) * ctx.width + (ctx.t * ctx.r + ctx.g))
          simpa only [b, Context.offset, TypeEnumeration.slotIndex,
            TypeEnumeration.headIndex, Bool.true_eq] using
            TypeIndexProgram.jointResult_output ctx.r ctx.width ctx.t ctx.g ctx.i a rfl rfl rfl rfl
        · by_cases h7 : j = 7
          · subst j; simp []
          · change (TypeIndexProgram.jointResult ctx.r ctx.t ctx.g ctx.i a).stacks j = _
            rw [TypeIndexProgram.jointResult_frame ctx.r ctx.t ctx.g ctx.i a j h1 h7]
            simp only [a,state,h1,ite_false]
      change Eval TypeIndexProgram.jointCommand
        (TypeIndexProgram.jointCost ctx.r ctx.width ctx.t ctx.g ctx.i) a b at ht
      rw [hb] at ht
      exact ⟨b.regs,ht⟩

def filterStacks (j : Fin 11) : Fin 16 := Fin.castAdd 5 j
theorem filterStacks_injective : Function.Injective filterStacks := Fin.castAdd_injective _ _

abbrev filterCommand (keep : Bool) : Cmd 8 16 :=
  .call (ProgramLinking.liftProgram (TypeBitFilter.program keep) id filterStacks)

theorem filter_eval (keep : Bool) (ctx : Context) (words : Records) (index : List Bool)
    (regs : Fin 8 → Bool) :
    ∃ n ≤ TypeBitFilter.budget keep words index.length, ∃ nextRegs,
      Eval (filterCommand keep) n (state ctx regs (ProgramEncoding.encodeRecords words) index [])
        (state ctx nextRegs (ProgramEncoding.encodeRecords words) index
          (ProgramEncoding.encodeRecords (words.filter (TypeBitFilter.test keep index.length)))) := by
  let a := state ctx regs (ProgramEncoding.encodeRecords words) index []
  obtain ⟨rf,hf⟩ := TypeBitFilter.program_runsIn keep words index regs
  have hi : restrictState id filterStacks a = TypeBitFilter.inputState words index regs := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [filterStacks,a,state]
  obtain ⟨n,hn,he⟩ := lifted_call (TypeBitFilter.program keep) id filterStacks
    Function.injective_id filterStacks_injective a (TypeBitFilter.outputState keep words index rf)
    (TypeBitFilter.budget keep words index.length) (by simpa only [hi] using hf)
  have ho : embedState id filterStacks a (TypeBitFilter.outputState keep words index rf) =
      state ctx rf (ProgramEncoding.encodeRecords words) index
        (ProgramEncoding.encodeRecords (words.filter (TypeBitFilter.test keep index.length))) := by
    apply SubexpScanPrimitives.embedState_eq _ _ Function.injective_id filterStacks_injective
    · intro j; rfl
    · intro j; fin_cases j <;> simp [state,filterStacks,TypeBitFilter.outputState]
    · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0,by simpa [filterStacks] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1,by simpa [filterStacks] using h.symm⟩
      have h10 : j ≠ 10 := fun h => hj ⟨10,by simpa [filterStacks] using h.symm⟩
      simp only [state,a,h0,h1,h10,ite_false]
  exact ⟨n,hn,rf,by simpa only [filterCommand,ho] using he⟩

abbrev command (joint : Bool) : Cmd 8 16 :=
  .seq (prepare joint) (.seq (filterCommand (!joint)) (.call (StackRoutines.clearProgram 1 3 4)))

def program (joint : Bool) := compiled (command joint) 0 10

def budget (joint : Bool) (ctx : Context) (words : Records) : ℕ :=
  prepareCost joint ctx + TypeBitFilter.budget (!joint) words (ctx.offset joint) +
    2 * ctx.offset joint + 4

theorem program_runsIn (joint : Bool) (ctx : Context) (words : Records) (regs : Fin 8 → Bool) :
    ∃ nextRegs, RunsIn (program joint) (budget joint ctx words)
      ((inputState ctx words regs).withPC (some (program joint).entry))
      ((outputState joint ctx words nextRegs).withPC none) := by
  obtain ⟨r1,h1⟩ := prepare_eval joint ctx (ProgramEncoding.encodeRecords words) regs
  obtain ⟨n,hn,r2,h2⟩ := filter_eval (!joint) ctx words (TypeIndexProgram.unary (ctx.offset joint)) r1
  let b := state ctx r2 (ProgramEncoding.encodeRecords words) (TypeIndexProgram.unary (ctx.offset joint))
    (ProgramEncoding.encodeRecords (resultWords joint ctx words))
  have h2' : Eval (filterCommand (!joint)) n
      (state ctx r1 (ProgramEncoding.encodeRecords words) (TypeIndexProgram.unary (ctx.offset joint)) []) b := by
    simpa only [TypeIndexProgram.unary,List.length_replicate,resultWords,b] using h2
  have h3 := clear_eval 1 3 4 b
  have hc : (⟨readRegs b.regs 3 4 none,StackRoutines.clearStacks 1 b.stacks⟩ : Data) =
      outputState joint ctx words (readRegs r2 3 4 none) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    by_cases hj : j = 1
    · subst j; rfl
    · simp only [StackRoutines.clearStacks,Function.update_of_ne hj,b,state,hj,ite_false]
  rw [hc] at h3
  have he := h1.seq (h2'.seq h3)
  refine ⟨readRegs r2 3 4 none,_,?_,compiled_halt_trace he 0 10⟩
  simp only [TypeIndexProgram.unary,List.length_replicate] at hn
  have hb1 : b.stacks 1 = List.replicate (ctx.offset joint) true := rfl
  rw [hb1,List.length_replicate]
  dsimp [budget]
  omega

theorem side_result (r Q Δ t g i : ℕ) :
    resultWords false ⟨r,t,g,Q*r,i⟩ (TypeEnumeration.universalBytes r Q Δ) =
      TypeEnumeration.sideBytes r Q Δ t g := by
  change List.filter (TypeBitFilter.test true (TypeEnumeration.headIndex r t g))
    (TypeEnumeration.universalBytes r Q Δ) = _
  apply congrArg (fun p : List Bool → Bool => (TypeEnumeration.universalBytes r Q Δ).filter p)
  funext bits
  simp [TypeBitFilter.test]

theorem joint_result (r Q Δ t g i : ℕ) :
    resultWords true ⟨r,t,g,Q*r,i⟩ (TypeEnumeration.sideBytes r Q Δ t g) =
      TypeEnumeration.jointBytes r Q Δ t g i := by
  change List.filter (TypeBitFilter.test false (TypeEnumeration.slotIndex r (Q * r) t g i))
    (TypeEnumeration.sideBytes r Q Δ t g) = _
  apply congrArg (fun p : List Bool → Bool => (TypeEnumeration.sideBytes r Q Δ t g).filter p)
  funext bits
  simp [TypeBitFilter.test]

theorem side_runsIn (r Q Δ t g i : ℕ) (regs : Fin 8 → Bool) :
    ∃ nextRegs, RunsIn (program false)
      (budget false ⟨r,t,g,Q*r,i⟩ (TypeEnumeration.universalBytes r Q Δ))
      ((inputState ⟨r,t,g,Q*r,i⟩ (TypeEnumeration.universalBytes r Q Δ) regs).withPC
        (some (program false).entry))
      ((state ⟨r,t,g,Q*r,i⟩ nextRegs
        (ProgramEncoding.encodeRecords (TypeEnumeration.universalBytes r Q Δ)) []
        (ProgramEncoding.encodeRecords (TypeEnumeration.sideBytes r Q Δ t g))).withPC none) := by
  simpa only [outputState,side_result] using
    program_runsIn false ⟨r,t,g,Q*r,i⟩ (TypeEnumeration.universalBytes r Q Δ) regs

theorem joint_runsIn (r Q Δ t g i : ℕ) (regs : Fin 8 → Bool) :
    ∃ nextRegs, RunsIn (program true)
      (budget true ⟨r,t,g,Q*r,i⟩ (TypeEnumeration.sideBytes r Q Δ t g))
      ((inputState ⟨r,t,g,Q*r,i⟩ (TypeEnumeration.sideBytes r Q Δ t g) regs).withPC
        (some (program true).entry))
      ((state ⟨r,t,g,Q*r,i⟩ nextRegs
        (ProgramEncoding.encodeRecords (TypeEnumeration.sideBytes r Q Δ t g)) []
        (ProgramEncoding.encodeRecords (TypeEnumeration.jointBytes r Q Δ t g i))).withPC none) := by
  simpa only [outputState,joint_result] using
    program_runsIn true ⟨r,t,g,Q*r,i⟩ (TypeEnumeration.sideBytes r Q Δ t g) regs

theorem primitive_runsIn (joint : Bool) (ctx : Context) (words : Records) (regs : Fin 8 → Bool) :
    ∃ nextRegs, Computation.RunsIn (BitProgram.primitive (program joint)).step
      (BitProgram.primitiveOverhead (program joint) * budget joint ctx words)
      (BitProgram.primitiveCfg (program joint)
        ((inputState ctx words regs).withPC (some (program joint).entry)))
      (BitProgram.primitiveCfg (program joint) ((outputState joint ctx words nextRegs).withPC none)) := by
  obtain ⟨nextRegs,h⟩ := program_runsIn joint ctx words regs
  exact ⟨nextRegs,BitProgram.primitive_execution (program joint) h⟩

end SubexponentialSAT.Subexp.TypeFiberProgram

end OAI.Algorithms
