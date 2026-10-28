import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramReadScalarBasic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramNormalize
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Exact native refinements for the scalar coefficient reader and injector.
All stacks outside the named outputs are preserved, including the ambient
low-product environment. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar
open BitProgram StructuredCalls
open HashCircuitProgram.Native

abbrev Machine := State 8 96

def readResult (d : Machine) (word tail : List Bool) : Machine :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks 79 tail) 80 word⟩

theorem read_eval (d : Machine) (word tail : List Bool)
    (hwidth : (d.stacks 12).length = word.length)
    (hsource : d.stacks 79 = word.reverse ++ tail)
    (h80 : d.stacks 80 = []) (h82 : d.stacks 82 = []) (h83 : d.stacks 83 = []) :
    Eval readScalar (11*word.length+8) d (readResult d word tail) := by
  let b := copied d 12 82
  have hcopy := copy_eval d 12 82 83 (by decide) (by decide) (by decide) h83
  have ht := ArrayPrograms.countedTransferProgram_trace (82 : Fin 96) 79 80
    (0 : Fin 8) 1 (by decide) (by decide) (by decide) (by decide)
    word.reverse tail (d.stacks 12) b.regs b.stacks
    (by simpa [b,copied,StackRoutines.copyStacks] using hsource)
    (by simp [b,copied,StackRoutines.copyStacks,h82])
    (by simpa using hwidth)
  have hh := StackRoutines.halt_after_trace _ ht 4 rfl rfl
  have hs : ArrayPrograms.countedTransferStacks (82 : Fin 96) 79 80
      word.reverse tail b.stacks = (readResult d word tail).stacks := by
    funext i
    by_cases h79 : i=79 <;> by_cases hi80 : i=80 <;> by_cases hi82 : i=82 <;>
      simp_all [ArrayPrograms.countedTransferStacks,b,copied,StackRoutines.copyStacks,
        readResult]
  have htransfer : Eval (.call (ArrayPrograms.countedTransferProgram
      (82 : Fin 96) 79 80 (0 : Fin 8) 1)) (4*word.length+3) b (readResult d word tail) := by
    apply Eval.call
    simp only [ArrayPrograms.countedTransferResult] at hh
    rw [hs] at hh
    simpa [StructuredProgram.State.withPC,readResult,b,copied,StackRoutines.readRegs_reset,
      ArrayPrograms.countedTransferProgram,Nat.add_assoc] using hh
  have h := hcopy.seq htransfer
  convert h using 1 ; simp only [hwidth] ; omega

@[simp] theorem injectPort_1 : injectPorts 1 = 82 := by decide
@[simp] theorem injectPort_2 : injectPorts 2 = 83 := by decide
@[simp] theorem injectPort_17 : injectPorts 17 = 17 := by decide
@[simp] theorem injectPort_31 : injectPorts 31 = 80 := by decide
@[simp] theorem injectPort_32 : injectPorts 32 = 81 := by decide
@[simp] theorem injectPort_37 : injectPorts 37 = 39 := by decide

def injectionCost (dimension zeroLength wordLength : ℕ) : ℕ :=
  7*dimension+6+(dimension-1)*(7*zeroLength+7)+6+(7*wordLength+5)+1

theorem inject_eval (d : Machine) (dimension : ℕ) (hd : 0 < dimension)
    (hdegree : d.stacks 39=List.replicate dimension true)
    (h82 : d.stacks 82=[]) (h83 : d.stacks 83=[]) (h81 : d.stacks 81=[]) :
    ∃ rf, Eval inject (injectionCost dimension (d.stacks 17).length (d.stacks 80).length) d
      ⟨rf,Function.update d.stacks 81
        (d.stacks 80 ++ Subexp.BlockCopyProgram.copies (dimension-1) (d.stacks 17))⟩ := by
  let a := projectState id injectPorts d
  obtain ⟨rf,ht⟩ := injectScalar_eval a dimension hd
    (by simpa [a,projectState] using hdegree)
    (by simpa [a,projectState] using h82)
    (by simpa [a,projectState] using h83)
    (by simpa [a,projectState] using h81)
  have he := eval_liftCommand_from_state injectScalar 31 32 id injectPorts d
    Function.injective_id injectPorts_injective ht
  let result : IdempotentPreparationProgram.Data :=
    ⟨rf,Function.update a.stacks 32
      (a.stacks 31 ++ Subexp.BlockCopyProgram.copies (dimension-1) (a.stacks 17))⟩
  have hb : embedState id injectPorts d result =
      (⟨rf,Function.update d.stacks 81
        (d.stacks 80 ++ Subexp.BlockCopyProgram.copies (dimension-1) (d.stacks 17))⟩ : Machine) := by
    apply embedState_eq_of_ports id injectPorts d _ result
      Function.injective_id injectPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i
      have hi : injectPorts i=81 ↔ i=32 := by
        rw [←injectPort_32,injectPorts_injective.eq_iff]
      simp [result,a,projectState,Function.update_apply,hi]
    · intro i hi
      have hi81 : i ≠ 81 := fun h => hi ⟨32,by simp [h]⟩
      simp [hi81]
  change Eval inject _ d (embedState id injectPorts d result) at he
  rw [hb] at he
  refine ⟨rf,?_⟩
  simpa [injectionCost,a,projectState] using he


theorem formatter_ports_injective (destination : Fin 96)
    (hdst : destination=61 ∨ destination=67) :
    Function.Injective (constantPorts destination) := by
  rcases hdst with rfl | rfl
  · exact constantPorts_61_injective
  · exact constantPorts_67_injective

def constantBytes (shapeLength : ℕ) (coeff : List Bool) : List Bool :=
  Encoding.frame (HashCircuitProgram.Constant.key shapeLength) ++ Encoding.frame coeff

theorem emit_eval (d : Machine) (destination : Fin 96)
    (hdst : destination=61 ∨ destination=67) (shape coeff : List Bool)
    (hshape : d.stacks 89=shape) (hcoeff : d.stacks 81=coeff)
    (h90 : d.stacks 90=[]) (h91 : d.stacks 91=[])
    (h92 : d.stacks 92=[]) (hout : d.stacks destination=[]) :
    ∃ rf, Eval (emitConstant destination) (8*shape.length+7*coeff.length+31) d
      ⟨rf,Function.update (Function.update (Function.update d.stacks 89 []) 81 [])
        destination (constantBytes shape.length coeff)⟩ := by
  have hi := formatter_ports_injective destination hdst
  have hp : projectState id (constantPorts destination) d =
      HashCircuitProgram.Constant.data d.regs shape [] [] coeff [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [constantPorts,
        hshape,hcoeff,h90,h91,h92,hout]
  obtain ⟨rf,h⟩ := HashCircuitProgram.Constant.command_eval d.regs shape coeff
  have ht := compiled_halt_trace h 0 5
  rw [←hp] at ht
  have he := eval_call_from_state HashCircuitProgram.Constant.program id
    (constantPorts destination) d Function.injective_id hi ht
  have hb : embedState id (constantPorts destination) d
      (HashCircuitProgram.Constant.data rf [] [] [] [] []
        (constantBytes shape.length coeff)) =
      (⟨rf,Function.update (Function.update (Function.update d.stacks 89 []) 81 [])
        destination (constantBytes shape.length coeff)⟩ : Machine) := by
    apply embedState_eq_of_ports id (constantPorts destination) d _ _
      Function.injective_id hi
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i
      rcases hdst with rfl | rfl <;> fin_cases i <;>
        simp [constantPorts,HashCircuitProgram.Constant.data,h90,h91,h92]
    · intro i hi
      have hi89 : i ≠ 89 := fun h => hi ⟨0,by simp [constantPorts,h]⟩
      have hi81 : i ≠ 81 := fun h => hi ⟨3,by simp [constantPorts,h]⟩
      have hidst : i ≠ destination := fun h => hi ⟨5,by simp [constantPorts,h]⟩
      simp [hi89,hi81,hidst]
  change Eval (emitConstant destination) _ d
    (embedState id (constantPorts destination) d
      (HashCircuitProgram.Constant.data rf [] [] [] [] [] (constantBytes shape.length coeff))) at he
  rw [hb] at he
  exact ⟨rf,by convert he using 1⟩

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar


namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar
open BitProgram StructuredCalls
open HashCircuitProgram.Native
open SubexpQuarticRing

def scalarWork (destination : Fin 96) : List (Fin 96) :=
  [70,80,81,82,83,89,90,91,92,destination]

def coefficient (dimension : ℕ) (zero word : List Bool) : List Bool :=
  word ++ Subexp.BlockCopyProgram.copies (dimension-1) zero

def scalarCost (dimension : ℕ) (zero word shape : List Bool) : ℕ :=
  (11*word.length+8) + injectionCost dimension zero.length word.length +
    (2*word.length+3) + (7*shape.length+5) +
    (8*shape.length+7*(coefficient dimension zero word).length+31)

/-- The scalar loader restores every work stack. Only the consumed source
prefix and the new constant dictionary differ from the caller state. -/
theorem scalar_eval (d : Machine) (destination : Fin 96)
    (hdst : destination=61 ∨ destination=67) (dimension : ℕ) (hd : 0 < dimension)
    (word tail : List Bool)
    (hwidth : (d.stacks 12).length=word.length)
    (hdegree : d.stacks 39=List.replicate dimension true)
    (hsource : d.stacks 79=word.reverse ++ tail)
    (hwork : ∀ i ∈ scalarWork destination, d.stacks i=[]) :
    ∃ rf, Eval (scalarConstant destination)
      (scalarCost dimension (d.stacks 17) word (d.stacks 88)) d
      ⟨rf,Function.update (Function.update d.stacks 79 tail) destination
        (constantBytes (d.stacks 88).length (coefficient dimension (d.stacks 17) word))⟩ := by
  have hw70 := hwork 70 (by simp [scalarWork])
  have hw80 := hwork 80 (by simp [scalarWork])
  have hw81 := hwork 81 (by simp [scalarWork])
  have hw82 := hwork 82 (by simp [scalarWork])
  have hw83 := hwork 83 (by simp [scalarWork])
  have hw89 := hwork 89 (by simp [scalarWork])
  have hw90 := hwork 90 (by simp [scalarWork])
  have hw91 := hwork 91 (by simp [scalarWork])
  have hw92 := hwork 92 (by simp [scalarWork])
  have hwdst := hwork destination (by simp [scalarWork])
  let b := readResult d word tail
  have h1 := read_eval d word tail hwidth hsource hw80 hw82 hw83
  obtain ⟨r2,h2⟩ := inject_eval b dimension hd
    (by simpa [b,readResult] using hdegree)
    (by simpa [b,readResult] using hw82)
    (by simpa [b,readResult] using hw83)
    (by simpa [b,readResult] using hw81)
  let c : Machine := ⟨r2,Function.update b.stacks 81 (coefficient dimension (d.stacks 17) word)⟩
  change Eval inject (injectionCost dimension (d.stacks 17).length word.length) b c at h2
  let e := cleared c 80
  have h3 := clear_eval c 80
  change Eval (clear 80) (2*word.length+3) c e at h3
  let f := copied e 88 89
  have h4 := copy_eval e 88 89 70 (by decide) (by decide) (by decide)
    (by simpa [e,cleared,c,b,readResult,StackRoutines.clearStacks] using hw70)
  change Eval (copy 88 89 70) (7*(d.stacks 88).length+5) e f at h4
  obtain ⟨rf,h5⟩ := emit_eval f destination hdst (d.stacks 88)
    (coefficient dimension (d.stacks 17) word)
    (by simp [f,copied,e,cleared,c,b,readResult,StackRoutines.copyStacks,
      StackRoutines.clearStacks,hw89])
    (by simp [f,copied,e,cleared,c,StackRoutines.copyStacks,StackRoutines.clearStacks])
    (by simpa [f,copied,e,cleared,c,b,readResult,StackRoutines.copyStacks,
      StackRoutines.clearStacks] using hw90)
    (by simpa [f,copied,e,cleared,c,b,readResult,StackRoutines.copyStacks,
      StackRoutines.clearStacks] using hw91)
    (by simpa [f,copied,e,cleared,c,b,readResult,StackRoutines.copyStacks,
      StackRoutines.clearStacks] using hw92)
    (by rcases hdst with rfl | rfl <;>
      simpa [f,copied,e,cleared,c,b,readResult,StackRoutines.copyStacks,
        StackRoutines.clearStacks] using hwdst)
  let g : Machine := ⟨rf,Function.update (Function.update (Function.update f.stacks 89 []) 81 [])
    destination (constantBytes (d.stacks 88).length (coefficient dimension (d.stacks 17) word))⟩
  change Eval (emitConstant destination) _ f g at h5
  have hg : g =
      (⟨rf,Function.update (Function.update d.stacks 79 tail) destination
        (constantBytes (d.stacks 88).length (coefficient dimension (d.stacks 17) word))⟩ : Machine) := by
    apply congrArg (StructuredProgram.State.mk rf)
    funext i
    rcases hdst with rfl | rfl <;>
      by_cases hi79 : i=79 <;> by_cases hi80 : i=80 <;>
      by_cases hi81 : i=81 <;> by_cases hi89 : i=89 <;>
      simp_all [g,f,copied,e,cleared,c,b,readResult,StackRoutines.copyStacks,
        StackRoutines.clearStacks,Function.update_apply]
  have h := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (Eval.base (StructuredProgram.Eval.skip g))))))
  change Eval (scalarConstant destination) _ d g at h
  rw [hg] at h
  exact ⟨rf,by convert h using 1 ; simp only [scalarCost] ; omega⟩

/-- The physical bytes are the standard singleton dictionary encoding. -/
theorem constantBytes_scalarVector {B dimension n : ℕ} (hd : 0 < dimension)
    (zero word : Word B) :
    constantBytes n (coefficient dimension zero.val word.val) =
      MomentsProgram.Normalize.bytes Squarefree.encodeIndex
        [(Squarefree.Index.origin (V := Fin n),scalarVector (d:=dimension) zero word)] := by
  unfold coefficient
  rw [←scalarVector_flat hd]
  simp [constantBytes,MomentsProgram.Normalize.bytes,Squarefree.Program.encodeDictionary,
    Squarefree.Program.rawEntries,HashCircuitProgram.Constant.key_eq_origin]


def wordCost (B dimension shapeLength : ℕ) : ℕ :=
  20*B+7*dimension+(dimension-1)*(7*B+7)+7*(dimension*B)+15*shapeLength+65

theorem scalarCost_words {B dimension : ℕ} (hd : 0 < dimension)
    (zero word : Word B) (shape : List Bool) :
    scalarCost dimension zero.val word.val shape = wordCost B dimension shape.length := by
  have hc : coefficient dimension zero.val word.val = RingProgram.flat (scalarVector (d:=dimension) zero word) :=
    (scalarVector_flat hd zero word).symm
  have hzlen : zero.val.length = B := zero.property
  have hwlen : word.val.length = B := word.property
  simp [scalarCost, injectionCost, hc, wordCost, hzlen, hwlen]
  ring

/-- Typed singleton bytes, with an explicit polynomial instruction count. -/
theorem scalar_words_eval {B dimension n : ℕ} (hd : 0 < dimension)
    (d : Machine) (destination : Fin 96) (hdst : destination=61 ∨ destination=67)
    (zero word : Word B) (tail : List Bool)
    (hwidth : (d.stacks 12).length=B) (hzero : d.stacks 17=zero.val)
    (hdegree : d.stacks 39=List.replicate dimension true)
    (hshape : (d.stacks 88).length=n)
    (hsource : d.stacks 79=word.val.reverse ++ tail)
    (hwork : ∀ i ∈ scalarWork destination, d.stacks i=[]) :
    ∃ rf, Eval (scalarConstant destination) (wordCost B dimension n) d
      ⟨rf,Function.update (Function.update d.stacks 79 tail) destination
        (MomentsProgram.Normalize.bytes Squarefree.encodeIndex
          [(Squarefree.Index.origin (V := Fin n),scalarVector (d:=dimension) zero word)])⟩ := by
  obtain ⟨rf,h⟩ := scalar_eval d destination hdst dimension hd word.val tail
    (by simpa only [word.property] using hwidth) hdegree hsource hwork
  rw [hzero,scalarCost_words hd, hshape,constantBytes_scalarVector hd] at h
  exact ⟨rf,h⟩

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar

end OAI.Algorithms
