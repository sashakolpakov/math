import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgramLoopReverse
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgramLookup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgramLift
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgramFrame

namespace OAI.Algorithms

/-! Assembly of one raw tuple term. All source lookup, coefficient lifting,
and record framing are executed by fixed native programs. The only persistent
data are the unexpanded original source, word width, modulus, ring shape,
unread raw bytes, and the already emitted output. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives

abbrev Data := State 8 24

def tapes (raw width modulus master shape acc quotient index payload shapeTmp : List Bool) :
    Fin 24 → List Bool :=
  ![raw,width,[],[],[],[],quotient,modulus,[],[],[],[],index,[],master,shape,
    acc,[],payload,shapeTmp,[],[],[],[]]

def data (regs : Fin 8 → Bool)
    (raw width modulus master shape acc quotient index payload shapeTmp : List Bool) : Data :=
  ⟨regs,tapes raw width modulus master shape acc quotient index payload shapeTmp⟩

theorem embed_tapes {r s : ℕ} (register : Fin r → Fin 8) (stack : Fin s → Fin 24)
    (hs : Function.Injective stack) (frame : Data) (source : State r s)
    (target : Fin 24 → List Bool)
    (hp : ∀ i, target (stack i) = source.stacks i)
    (hf : ∀ i, (¬ ∃ j, stack j = i) → target i = frame.stacks i) :
    embedState register stack frame source =
      (⟨(embedState register stack frame source).regs,target⟩ : Data) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    by_cases hi : ∃ j, stack j = i
    · obtain ⟨j,rfl⟩ := hi
      exact (embedState_stack register stack frame source hs j).trans (hp j).symm
    · exact (embedState_stack_frame register stack frame source i hi).trans (hf i hi).symm

def decoderStacks : Fin 14 → Fin 24 := Fin.castAdd 10
theorem decoderStacks_injective : Function.Injective decoderStacks := Fin.castAdd_injective _ _
abbrev decode : Cmd 8 24 := .call (ProgramLinking.liftProgram
  LoopDecode.reversedProgram id decoderStacks)

theorem decode_eval (regs : Fin 8 → Bool)
    (word rest width modulus master shape acc : List Bool)
    (hw : width.length=word.length) (hm : 0 < SubexponentialSAT.BinaryArithmetic.toNat modulus) :
    ∃ n ≤ LoopDecode.budget word.length modulus.length (SubexponentialSAT.BinaryArithmetic.toNat modulus)+
        9*word.length+8, ∃ rf,
      Eval decode n (data regs (word.reverse++rest) width modulus master shape acc [] [] [] [])
        (data rf rest width modulus master shape acc
          (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1
          (Encoding.encodeNat (SubexponentialSAT.BinaryArithmetic.toNat word %
            SubexponentialSAT.BinaryArithmetic.toNat modulus)) [] []) := by
  let d := data regs (word.reverse++rest) width modulus master shape acc [] [] [] []
  obtain ⟨rf,n,hn,ht⟩ := LoopDecode.reversedProgram_runs regs word rest width modulus hw hm
  have hi : projectState id decoderStacks d =
      LoopDecode.data regs (word.reverse++rest) width modulus [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> rfl
  rw [← hi] at ht
  have he := eval_call_from_state LoopDecode.reversedProgram id decoderStacks d
    Function.injective_id decoderStacks_injective ht
  have ho := embed_tapes id decoderStacks decoderStacks_injective d
    (LoopDecode.data rf rest width modulus [] []
      (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1
      (Encoding.encodeNat (SubexponentialSAT.BinaryArithmetic.toNat word % SubexponentialSAT.BinaryArithmetic.toNat modulus)))
    (tapes rest width modulus master shape acc
      (SubexponentialSAT.ModularQuotientArithmetic.divide modulus word).1
      (Encoding.encodeNat (SubexponentialSAT.BinaryArithmetic.toNat word % SubexponentialSAT.BinaryArithmetic.toNat modulus)) [] [])
    (by intro i; fin_cases i <;> rfl)
    (by
      intro i h
      have h0 : i ≠ 0 := fun hh => h ⟨0,hh.symm⟩
      have h6 : i ≠ 6 := fun hh => h ⟨6,hh.symm⟩
      have h12 : i ≠ 12 := fun hh => h ⟨12,hh.symm⟩
      fin_cases i <;> simp_all [d,data,tapes])
  rw [ho] at he
  exact ⟨n,hn,_,he⟩

def lowRegisters : Fin 3 → Fin 8 := Fin.castAdd 5
theorem lowRegisters_injective : Function.Injective lowRegisters := Fin.castAdd_injective _ _
def lookupStacks : Fin 6 → Fin 24 := ![14,8,12,9,10,18]
theorem lookupStacks_injective : Function.Injective lookupStacks := by decide
abbrev lookup : Cmd 8 24 := .call (ProgramLinking.liftProgram
  Source.fetchProgram lowRegisters lookupStacks)

theorem lookup_eval (regs : Fin 8 → Bool) (clauses : List (List Bool))
    (i : Fin clauses.length) (rest width modulus shape acc quotient : List Bool) :
    ∃ n ≤ 23*(Encoding.encodeList id clauses).length+19, ∃ rf,
      Eval lookup n
        (data regs rest width modulus (Encoding.encodeList id clauses) shape acc quotient
          (Encoding.encodeNat i.val) [] [])
        (data rf rest width modulus (Encoding.encodeList id clauses) shape acc quotient
          [] clauses[i.val] []) := by
  let d := data regs rest width modulus (Encoding.encodeList id clauses) shape acc quotient
    (Encoding.encodeNat i.val) [] []
  obtain ⟨flag,n,hn,ht⟩ := Source.fetch_original_runs clauses i (regs 0) (regs 1) (regs 2)
  have hi : projectState lowRegisters lookupStacks d =
      Source.data (regs 0) (regs 1) (regs 2) (Encoding.encodeList id clauses) []
        (Encoding.encodeNat i.val) [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j <;> rfl
  rw [← hi] at ht
  have he := eval_call_from_state Source.fetchProgram lowRegisters lookupStacks d
    lowRegisters_injective lookupStacks_injective ht
  have ho := embed_tapes lowRegisters lookupStacks lookupStacks_injective d
    (Source.data false false flag (Encoding.encodeList id clauses) [] [] [] [] clauses[i.val])
    (tapes rest width modulus (Encoding.encodeList id clauses) shape acc quotient [] clauses[i.val] [])
    (by intro j; fin_cases j <;> rfl)
    (by
      intro j h
      have h12 : j ≠ 12 := fun hh => h ⟨2,hh.symm⟩
      have h18 : j ≠ 18 := fun hh => h ⟨5,hh.symm⟩
      fin_cases j <;> simp_all [d,data,tapes])
  rw [ho] at he
  exact ⟨n,hn,_,he⟩

abbrev copyShape : Cmd 8 24 := .call (StackRoutines.copyProgram 15 19 20 0 1)

theorem copyShape_eval (regs : Fin 8 → Bool)
    (rest width modulus master shape acc quotient payload : List Bool) :
    Eval copyShape (7*shape.length+5)
      (data regs rest width modulus master shape acc quotient [] payload [])
      (data (readRegs regs 0 1 none) rest width modulus master shape acc quotient [] payload shape) := by
  have h := copy_eval (data regs rest width modulus master shape acc quotient [] payload [])
    15 19 20 0 1 (by decide) (by decide) (by decide) (by decide) rfl
  convert h using 1
  · simp [data, tapes]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [data,tapes,StackRoutines.copyStacks]

def normalizationStacks : Fin 8 → Fin 24 := ![6,8,9,10,11,13,20,19]
theorem normalizationStacks_injective : Function.Injective normalizationStacks := by decide
abbrev normalize : Cmd 8 24 := .call (ProgramLinking.liftProgram
  SubexponentialSAT.ModularRingPrograms.normalizeProgram id normalizationStacks)

theorem normalize_eval (t d : ℕ) (ht : 0 < t) (c : ZMod 3) (regs : Fin 8 → Bool)
    (rest width modulus master shape acc quotient payload : List Bool)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t)
    (hq : SubexponentialSAT.BinaryArithmetic.toNat quotient=c.val) :
    ∃ n ≤ 7*shape.length+2*quotient.length+9, ∃ rf,
      Eval normalize n
        (data regs rest width modulus master shape acc quotient [] payload shape)
        (data rf rest width modulus master shape acc
          (RingProgram.flat (constantVector t d c)) [] payload []) := by
  let a := data regs rest width modulus master shape acc quotient [] payload shape
  obtain ⟨rf,n,hn,hr⟩ := lift_runs t d ht c shape quotient [] hshape hq regs
  have hi : projectState id normalizationStacks a =
      (⟨regs,SubexponentialSAT.ModularRingPrograms.normalizationState quotient shape [] []⟩ : State 8 8) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> rfl
  change Trace SubexponentialSAT.ModularRingPrograms.normalizeProgram n
    ((⟨regs,SubexponentialSAT.ModularRingPrograms.normalizationState quotient shape [] []⟩ : State 8 8).withPC
      (some SubexponentialSAT.ModularRingPrograms.normalizeProgram.entry))
    ((⟨rf,SubexponentialSAT.ModularRingPrograms.normalizationState
      (RingProgram.flat (constantVector t d c)) [] [] []⟩ : State 8 8).withPC none) at hr
  rw [← hi] at hr
  have he := eval_call_from_state SubexponentialSAT.ModularRingPrograms.normalizeProgram id normalizationStacks a
    Function.injective_id normalizationStacks_injective hr
  have ho := embed_tapes id normalizationStacks normalizationStacks_injective a
    (⟨rf,SubexponentialSAT.ModularRingPrograms.normalizationState
      (RingProgram.flat (constantVector t d c)) [] [] []⟩ : State 8 8)
    (tapes rest width modulus master shape acc (RingProgram.flat (constantVector t d c)) [] payload [])
    (by intro i; fin_cases i <;> rfl)
    (by
      intro i h
      have h6 : i ≠ 6 := fun hh => h ⟨0,hh.symm⟩
      have h19 : i ≠ 19 := fun hh => h ⟨7,hh.symm⟩
      fin_cases i <;> simp_all [a,data,tapes])
  rw [ho] at he
  exact ⟨n,hn,_,he⟩

def frameStacks : Fin 3 → Fin 24 := ![6,18,8]
theorem frameStacks_injective : Function.Injective frameStacks := by decide
abbrev frameWeight : Cmd 8 24 := .call (ProgramLinking.liftProgram
  Frame.program lowRegisters frameStacks)

theorem frameWeight_eval (regs : Fin 8 → Bool)
    (rest width modulus master shape acc weight payload : List Bool) :
    ∃ n ≤ 7*weight.length+10, ∃ rf,
      Eval frameWeight n (data regs rest width modulus master shape acc weight [] payload [])
        (data rf rest width modulus master shape acc [] [] (Encoding.frame weight++payload) []) := by
  let a := data regs rest width modulus master shape acc weight [] payload []
  obtain ⟨rf,n,hn,hr⟩ := Frame.program_runs (regs ∘ lowRegisters) weight payload
  have hi : projectState lowRegisters frameStacks a =
      Frame.data (regs ∘ lowRegisters) weight payload [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> rfl
  rw [← hi] at hr
  have he := eval_call_from_state Frame.program lowRegisters frameStacks a
    lowRegisters_injective frameStacks_injective hr
  have ho := embed_tapes lowRegisters frameStacks frameStacks_injective a
    (Frame.data rf [] (Encoding.frame weight++payload) [])
    (tapes rest width modulus master shape acc [] [] (Encoding.frame weight++payload) [])
    (by intro i; fin_cases i <;> rfl)
    (by
      intro i h
      have h6 : i ≠ 6 := fun hh => h ⟨0,hh.symm⟩
      have h18 : i ≠ 18 := fun hh => h ⟨1,hh.symm⟩
      fin_cases i <;> simp_all [a,data,tapes])
  rw [ho] at he
  exact ⟨n,hn,_,he⟩

def recordStacks : Fin 3 → Fin 24 := ![18,16,8]
theorem recordStacks_injective : Function.Injective recordStacks := by decide
abbrev frameRecord : Cmd 8 24 := .call (ProgramLinking.liftProgram
  Frame.program lowRegisters recordStacks)

theorem frameRecord_eval (regs : Fin 8 → Bool)
    (rest width modulus master shape acc payload : List Bool) :
    ∃ n ≤ 7*payload.length+10, ∃ rf,
      Eval frameRecord n (data regs rest width modulus master shape acc [] [] payload [])
        (data rf rest width modulus master shape (Encoding.frame payload++acc) [] [] [] []) := by
  let a := data regs rest width modulus master shape acc [] [] payload []
  obtain ⟨rf,n,hn,hr⟩ := Frame.program_runs (regs ∘ lowRegisters) payload acc
  have hi : projectState lowRegisters recordStacks a =
      Frame.data (regs ∘ lowRegisters) payload acc [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> rfl
  rw [← hi] at hr
  have he := eval_call_from_state Frame.program lowRegisters recordStacks a
    lowRegisters_injective recordStacks_injective hr
  have ho := embed_tapes lowRegisters recordStacks recordStacks_injective a
    (Frame.data rf [] (Encoding.frame payload++acc) [])
    (tapes rest width modulus master shape (Encoding.frame payload++acc) [] [] [] [])
    (by intro i; fin_cases i <;> rfl)
    (by
      intro i h
      have h16 : i ≠ 16 := fun hh => h ⟨1,hh.symm⟩
      have h18 : i ≠ 18 := fun hh => h ⟨0,hh.symm⟩
      fin_cases i <;> simp_all [a,data,tapes])
  rw [ho] at he
  exact ⟨n,hn,_,he⟩

abbrev tagRecord : Cmd 8 24 := .seq (.base (.atom (.set 0 true))) (.base (.atom (.push 16 0)))

theorem tagRecord_eval (regs : Fin 8 → Bool)
    (rest width modulus master shape acc : List Bool) :
    Eval tagRecord 2 (data regs rest width modulus master shape acc [] [] [] [])
      (data (Function.update regs 0 true) rest width modulus master shape (true::acc) [] [] [] []) := by
  let a := data regs rest width modulus master shape acc [] [] [] []
  let b := (StructuredProgram.Atom.set (0 : Fin 8) true).eval a
  have h1 : Eval (.base (.atom (.set 0 true))) 1 a b := .base (.atom _ _)
  have h2 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.push (16 : Fin 24) 0) b)
  have he := h1.seq h2
  convert he using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [a,b,data,tapes,StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr]

end SubexponentialSAT.SqrtLog.HashInputProgram.Loop

end OAI.Algorithms
