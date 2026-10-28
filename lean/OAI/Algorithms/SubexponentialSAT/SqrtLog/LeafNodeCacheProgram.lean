import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramConstant
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorageCost
import OAI.Algorithms.SubexponentialSAT.BankRoutines

namespace OAI.Algorithms

/-! Physical staging of node-local cached ring words. The ambient source tapes
and ring masters are copied, never consumed. The two raw-one caches are built
by the checked sparse-constant program, rather than supplied semantically. -/
namespace SubexponentialSAT.SqrtLog.LeafNodeCacheProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev LocalData := State 16 768
abbrev Data := State 40 768

def directCopies : List (Fin 768 × Fin 768) :=
  [(194,5),(202,12),(203,17),(201,22),(204,39),(212,45),(243,46),
   (211,76),(281,143),(128,88),(280,190),(128,191)]
def copies : List (Fin 768 × Fin 768) := directCopies ++ [(128,340),(207,343)]
def cachePorts : List (Fin 768) := [5,12,17,22,39,45,46,76,143,88,190,191,69,167]
def pocket : List (Fin 768) := [340,341,342,343,344,345,346]
def Ready (f : Fin 768 → List Bool) : Prop := ∀ i ∈ cachePorts ++ pocket, f i = []

def rawOne (f : Fin 768 → List Bool) :=
  Encoding.frame (HashCircuitProgram.Constant.key (f 128).length) ++ Encoding.frame (f 207)

def constantRegisters : Fin 8 → Fin 16 := Fin.castAdd 8
def constantStacks (i : Fin 6) : Fin 768 := ⟨340+i.val,by omega⟩
theorem constantStacks_injective : Function.Injective constantStacks := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [constantStacks] at this
  omega

abbrev constant : Cmd 16 768 :=
  .call (ProgramLinking.liftProgram HashCircuitProgram.Constant.program constantRegisters constantStacks)
abbrev prepare : Cmd 16 768 := copyMany 346 copies
abbrev duplicate : Cmd 16 768 := copyMany 346 [(345,69),(345,167)]
abbrev finish : Cmd 16 768 := clearCmd 345
abbrev localCommand : Cmd 16 768 := .seq prepare (.seq constant (.seq duplicate finish))

def prepared (a : LocalData) : LocalData := copyManyState copies a

def constantTapes (f : Fin 768 → List Bool) (word : List Bool) : Fin 768 → List Bool :=
  fun i => if i=345 then word else if 340 ≤ i.val ∧ i.val < 345 then [] else f i

noncomputable def constantResult (a : LocalData) (rr : Fin 8 → Bool) (word : List Bool) : LocalData :=
  ⟨Function.extend constantRegisters rr a.regs,constantTapes a.stacks word⟩

noncomputable def finalState (a : LocalData) (rr : Fin 8 → Bool) (word : List Bool) : LocalData :=
  clearState 345 (copyManyState [(345,69),(345,167)] (constantResult a rr word))

def localBudget (a : LocalData) := copyManyCost copies a +
  (8*(a.stacks 128).length+7*(a.stacks 207).length+31) + 16*(rawOne a.stacks).length+13

private theorem prepared_word (a : LocalData) (h : Ready a.stacks) :
    (prepared a).stacks 340 = a.stacks 128 ∧
    (prepared a).stacks 343 = a.stacks 207 ∧
    (∀ i ∈ ([341,342,344,345,346,69,167] : List (Fin 768)), (prepared a).stacks i=[]) := by
  have h340 := h 340 (by decide)
  have h343 := h 343 (by decide)
  constructor
  · simp [prepared,copies,directCopies,copyManyState,copyState,StackRoutines.copyStacks,h340]
  constructor
  · simp [prepared,copies,directCopies,copyManyState,copyState,StackRoutines.copyStacks,h343]
  · intro i hi
    have hi' : i=341 ∨ i=342 ∨ i=344 ∨ i=345 ∨ i=346 ∨ i=69 ∨ i=167 := by simpa using hi
    rcases hi' with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simpa [prepared,copies,directCopies,copyManyState,copyState,StackRoutines.copyStacks] using h 341 (by decide)
    · simpa [prepared,copies,directCopies,copyManyState,copyState,StackRoutines.copyStacks] using h 342 (by decide)
    · simpa [prepared,copies,directCopies,copyManyState,copyState,StackRoutines.copyStacks] using h 344 (by decide)
    · simpa [prepared,copies,directCopies,copyManyState,copyState,StackRoutines.copyStacks] using h 345 (by decide)
    · simpa [prepared,copies,directCopies,copyManyState,copyState,StackRoutines.copyStacks] using h 346 (by decide)
    · simpa [prepared,copies,directCopies,copyManyState,copyState,StackRoutines.copyStacks] using h 69 (by decide)
    · simpa [prepared,copies,directCopies,copyManyState,copyState,StackRoutines.copyStacks] using h 167 (by decide)

private theorem constant_embed (a : LocalData) (rr : Fin 8 → Bool) (word : List Bool) :
    embedState constantRegisters constantStacks a
      (HashCircuitProgram.Constant.data rr [] [] [] [] [] word) = constantResult a rr word := by
  apply embedState_eq_of_ports _ _ _ _ _ (Fin.castAdd_injective _ _) constantStacks_injective
  · intro i
    exact (Fin.castAdd_injective _ _).extend_apply _ _ i
  · intro i hi
    exact Function.extend_apply' _ _ _ hi
  · intro i; fin_cases i  <;> simp [constantStacks,constantResult,constantTapes,HashCircuitProgram.Constant.data]
  · intro i hi
    have hn (j : Fin 6) : i ≠ constantStacks j := fun h => hi ⟨j,h.symm⟩
    have h345 : i ≠ 345 := hn 5
    have hr : ¬(340 ≤ i.val ∧ i.val < 345) := by
      rintro ⟨hl,hu⟩
      have he : i = constantStacks ⟨i.val-340,by omega⟩ := by apply Fin.ext; simp [constantStacks]; omega
      exact hn _ he
    simp [constantResult,constantTapes,h345,hr]

private theorem constant_eval (a : LocalData) (h : Ready a.stacks) :
    ∃ rr, Eval constant (8*(a.stacks 128).length+7*(a.stacks 207).length+31)
      (prepared a) (constantResult (prepared a) rr (rawOne a.stacks)) := by
  obtain ⟨h340,h343,hrest⟩ := prepared_word a h
  obtain ⟨rr,he⟩ := HashCircuitProgram.Constant.command_eval
    ((prepared a).regs ∘ constantRegisters) (a.stacks 128) (a.stacks 207)
  have hp : project constantRegisters constantStacks (prepared a) =
      HashCircuitProgram.Constant.data ((prepared a).regs ∘ constantRegisters)
        (a.stacks 128) [] [] (a.stacks 207) [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i  <;>
        simpa [project,constantStacks,HashCircuitProgram.Constant.data] using
          (show (prepared a).stacks _ = _ from by first | exact h340 | exact h343 | exact hrest _ (by decide))
  have ht := compiled_halt_trace he 0 5
  rw [← hp] at ht
  have hc := invoke_eval HashCircuitProgram.Constant.program constantRegisters constantStacks
    (Fin.castAdd_injective _ _) constantStacks_injective (prepared a) _ ht
  refine ⟨rr,?_⟩
  simpa [constant,invoke,constant_embed,rawOne,Nat.add_assoc] using hc

/-- Every copy, sparse-constant construction and private-pocket clear is paid.
The theorem applies to arbitrary external frames and arbitrary registers. -/
theorem local_eval (a : LocalData) (h : Ready a.stacks) :
    ∃ rr, Eval localCommand (localBudget a) a
      (finalState (prepared a) rr (rawOne a.stacks)) := by
  have htmp := h 346 (by decide)
  have hp := copyMany_eval (346:Fin 768) copies a (by simp [copies,directCopies]) htmp
  obtain ⟨rr,hc⟩ := constant_eval a h
  have hrest := (prepared_word a h).2.2
  let b := constantResult (prepared a) rr (rawOne a.stacks)
  have hbtemp : b.stacks 346=[] := by simp [b,constantResult,constantTapes,hrest 346 (by decide)]
  have hd := copyMany_eval (346:Fin 768) [(345,69),(345,167)] b (by simp) hbtemp
  have hf := clear_eval (345:Fin 768) (copyManyState [(345,69),(345,167)] b)
  have hdCost : copyManyCost [(345,69),(345,167)] b = 14*(rawOne a.stacks).length+10 := by
    simp [copyManyCost,copyState,StackRoutines.copyStacks,b,constantResult,constantTapes]
    omega
  have hfCost : 2*((copyManyState [(345,69),(345,167)] b).stacks 345).length+3 =
      2*(rawOne a.stacks).length+3 := by
    simp [copyManyState,copyState,StackRoutines.copyStacks,b,constantResult,constantTapes]
  have ht : copyManyCost copies a +
      ((8*(a.stacks 128).length+7*(a.stacks 207).length+31) +
        (copyManyCost [(345,69),(345,167)] b +
          (2*((copyManyState [(345,69),(345,167)] b).stacks 345).length+3))) = localBudget a := by
    rw [hdCost,hfCost]
    unfold localBudget
    omega
  have he := hp.seq (hc.seq (hd.seq hf))
  rw [ht] at he
  exact ⟨rr,he⟩


end SubexponentialSAT.SqrtLog.LeafNodeCacheProgram

end OAI.Algorithms
