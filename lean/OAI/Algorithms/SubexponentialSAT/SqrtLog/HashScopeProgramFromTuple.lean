import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramNativeSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramSingle
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramReset
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgramLoopFinal

namespace OAI.Algorithms

/-! Direct original-source-to-scope composition. The finite program first reads
raw tuple references and looks up original clauses, then extracts their scope.
No table of precomputed scopes is supplied to this machine. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.FromTuple
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)

abbrev Data := State 11 46

def assemblyRegisters : Fin 8 → Fin 11 := Fin.castAdd 3
def assemblyStacks : Fin 24 → Fin 46 := Fin.castAdd 22

def scopeStacks (i : Fin 22) : Fin 46 :=
  if i=19 then 16 else ⟨i.val+24,by omega⟩

theorem assemblyRegisters_injective : Function.Injective assemblyRegisters :=
  Fin.castAdd_injective _ _
theorem assemblyStacks_injective : Function.Injective assemblyStacks :=
  Fin.castAdd_injective _ _
theorem scopeStacks_injective : Function.Injective scopeStacks := by decide

def extend (a : State 8 24) : Data :=
  ⟨fun i => if h : i.val < 8 then a.regs ⟨i.val,h⟩ else false,
    fun i => if h : i.val < 24 then a.stacks ⟨i.val,h⟩ else []⟩

abbrev assembly : Cmd 11 46 := .call (ProgramLinking.liftProgram HashInputProgram.Loop.assembleProgram
  assemblyRegisters assemblyStacks)
abbrev extract : Cmd 11 46 := .call (ProgramLinking.liftProgram Single.program id scopeStacks)
abbrev clearEll : Cmd 11 46 := .call (StackRoutines.clearProgram 42 8 9)
abbrev command : Cmd 11 46 := .seq assembly (.seq Reset.all (.seq extract clearEll))
def program := compiled command 0 16

private theorem restrict_extend (a : State 8 24) :
    restrictState assemblyRegisters assemblyStacks (extend a)=a := by
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext i; simp [restrictState,extend,assemblyRegisters,i.isLt]
  · funext i; simp [restrictState,extend,assemblyStacks,i.isLt]

private theorem embed_extend (a b : State 8 24) :
    embedState assemblyRegisters assemblyStacks (extend a) b=extend b := by
  apply embedState_eq_of_ports _ _ _ _ _ assemblyRegisters_injective assemblyStacks_injective
  · intro i; simp [extend,assemblyRegisters,i.isLt]
  · intro i hi
    have hn : ¬i.val < 8 := by
      intro h
      exact hi ⟨⟨i.val,h⟩,Fin.ext rfl⟩
    simp [extend,hn]
  · intro i; simp [extend,assemblyStacks,i.isLt]
  · intro i hi
    have hn : ¬i.val < 24 := by
      intro h
      exact hi ⟨⟨i.val,h⟩,Fin.ext rfl⟩
    simp [extend,hn]


def scopeState (rf : Fin 11 → Bool) (a : Data) (bits : List Bool) : Data :=
  ⟨rf,fun i => if i=16 then bits else if i=42 then [true] else a.stacks i⟩

private theorem extract_eval (terms : List Term) (a : Data)
    (hr : a.regs=fun _ => false)
    (hs : a.stacks 16=Encoding.encodeList payload terms)
    (he : ∀ i : Fin 22, i≠19 → a.stacks (scopeStacks i)=[]) :
    ∃ n ≤ Single.cost terms, ∃ rf,
      Eval extract n a (scopeState rf a (Encoding.encodeList Encoding.encodeNat (scope terms))) := by
  obtain ⟨rf,ht⟩ := Single.program_runsIn terms
  let localState : State 11 22 := ⟨rf,SubexponentialSAT.SubexpChunkRecordMap.tapes [true]
    (Encoding.encodeList Encoding.encodeNat (scope terms)) [] []⟩
  have ha : restrictState id scopeStacks a=
      SubexponentialSAT.SubexpChunkRecordMap.data false false false [] (Encoding.encodeList payload terms) [] [] := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · funext i; simp [restrictState,hr,SubexponentialSAT.SubexpChunkRecordMap.data,SubexponentialSAT.SubexpChunkRecordMap.regs]
    · funext i
      by_cases hi : i=19
      · subst i; simpa [restrictState,scopeStacks,SubexponentialSAT.SubexpChunkRecordMap.data,
          SubexponentialSAT.SubexpChunkRecordMap.tapes] using hs
      · simpa [restrictState,SubexponentialSAT.SubexpChunkRecordMap.data,SubexponentialSAT.SubexpChunkRecordMap.tapes,hi]
          using he i hi
  obtain ⟨n,hn,hh⟩ := lifted_call Single.program id scopeStacks Function.injective_id
    scopeStacks_injective a localState (Single.cost terms) (by simpa [ha,localState] using ht)
  have hb : embedState id scopeStacks a localState=
      scopeState rf a (Encoding.encodeList Encoding.encodeNat (scope terms)) := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id scopeStacks_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
    · intro i
      have hei := he i
      fin_cases i <;> simp_all [scopeState,scopeStacks,localState,SubexponentialSAT.SubexpChunkRecordMap.tapes]
    · intro i hi
      have h16 : i≠16 := fun h => hi ⟨19,h.symm⟩
      have h42 : i≠42 := fun h => hi ⟨18,h.symm⟩
      simp [scopeState,h16,h42]
  exact ⟨n,hn,rf,by simpa [hb] using hh⟩

def finished (rf : Fin 11 → Bool) (width modulus master shape bits : List Bool) : Data :=
  ⟨rf,(extend (HashInputProgram.Loop.data (fun _ => false) [] width modulus master shape
    bits [] [] [] [])).stacks⟩

private theorem clearEll_eval (rf : Fin 11 → Bool)
    (width modulus master shape oldBits bits : List Bool) :
    Eval clearEll 5
      (scopeState rf (finished (fun _ => false) width modulus master shape oldBits) bits)
      (finished (readRegs rf 8 9 none) width modulus master shape bits) := by
  have hh := SubexponentialSAT.Subexp.TupleProgram.clear_eval (42 : Fin 46) (8 : Fin 11) 9
    (scopeState rf (finished (fun _ => false) width modulus master shape oldBits) bits)
  convert hh using 1
  · simp [scopeState]
  · apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · rfl
    · funext i; fin_cases i <;> rfl

def cost (t d b : ℕ) (modulus : List Bool) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ) (terms : List (Fin clauses.length × ZMod 3)) : ℕ :=
  HashInputProgram.Loop.uniformBudget t d b modulus clauses terms.length+20+
    Single.cost (interpretedTerms (clauses := clauses) t d codes terms)

/-- The output is produced from raw references and the unexpanded original
clause bytes, including every zero-coefficient and repeated reference. -/
theorem state_runsIn (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (terms : List (Fin clauses.length × ZMod 3))
    (hbound : 3*clauses.length ≤ 2^b) (regs : Fin 8 → Bool)
    (width modulus shape : List Bool) (hw : width.length=b)
    (hm : BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ rf, RunsIn program (cost t d b modulus clauses codes terms)
      ((extend (HashInputProgram.Loop.data regs (HashInputProgram.Loop.rawInput b terms) width modulus
        (Encoding.encodeList id clauses) shape [] [] [] [] [])).withPC (some program.entry))
      ((finished rf width modulus (Encoding.encodeList id clauses) shape
        (Encoding.encodeList Encoding.encodeNat
          (scope (interpretedTerms (clauses := clauses) t d codes terms)))).withPC none) := by
  let initial := HashInputProgram.Loop.data regs (HashInputProgram.Loop.rawInput b terms) width modulus
    (Encoding.encodeList id clauses) shape [] [] [] [] []
  obtain ⟨rf,hassemble⟩ := HashInputProgram.Loop.assemble_runs t d ht b hb clauses terms hbound regs
    width modulus shape hw hm hshape
  let middle := HashInputProgram.Loop.data rf [] width modulus (Encoding.encodeList id clauses) shape
    (Encoding.encodeList id (terms.map (HashInputProgram.Loop.payload t d clauses))) [] [] [] []
  obtain ⟨na,hna,hea⟩ := lifted_call HashInputProgram.Loop.assembleProgram assemblyRegisters assemblyStacks
    assemblyRegisters_injective assemblyStacks_injective (extend initial) middle
    (HashInputProgram.Loop.uniformBudget t d b modulus clauses terms.length+3)
    (by simpa [restrict_extend,initial,middle] using hassemble)
  rw [embed_extend] at hea
  let clean : Data := ⟨fun _ => false,(extend middle).stacks⟩
  have her : Eval (Reset.all : Cmd 11 46) 11 (extend middle) clean := Reset.all_eval _
  obtain ⟨ns,hns,rs,hes⟩ := extract_eval (interpretedTerms (clauses := clauses) t d codes terms) clean rfl
    (by simpa [clean,extend,middle,HashInputProgram.Loop.data,HashInputProgram.Loop.tapes] using
      (interpreted_payload t d clauses codes hc terms).symm)
    (by intro i hi; simp [clean,extend,scopeStacks,hi])
  have hclear := clearEll_eval rs width modulus (Encoding.encodeList id clauses) shape
    (Encoding.encodeList id (terms.map (HashInputProgram.Loop.payload t d clauses)))
    (Encoding.encodeList Encoding.encodeNat (scope (interpretedTerms (clauses := clauses) t d codes terms)))
  refine ⟨readRegs rs 8 9 none,na+(11+(ns+5))+1,?_,?_⟩
  · unfold cost; omega
  · exact compiled_halt_trace (hea.seq (her.seq (hes.seq hclear))) 0 16



theorem primitive_runsIn (t d : ℕ) (ht : 0 < t) (b : ℕ) (hb : 0 < b)
    (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (terms : List (Fin clauses.length × ZMod 3))
    (hbound : 3*clauses.length ≤ 2^b) (regs : Fin 8 → Bool)
    (width modulus shape : List Bool) (hw : width.length=b)
    (hm : BinaryArithmetic.toNat modulus=clauses.length)
    (hshape : shape.length=(d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) :
    ∃ final : Data,
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * cost t d b modulus clauses codes terms)
        (primitiveCfg program
          ((extend (HashInputProgram.Loop.data regs (HashInputProgram.Loop.rawInput b terms) width modulus
            (Encoding.encodeList id clauses) shape [] [] [] [] [])).withPC (some program.entry)))
        (primitiveCfg program (final.withPC none)) ∧
      final.stacks 16=Encoding.encodeList Encoding.encodeNat
        (scope (interpretedTerms (clauses := clauses) t d codes terms)) ∧
      final.stacks 14=Encoding.encodeList id clauses := by
  obtain ⟨rf,h⟩ := state_runsIn t d ht b hb clauses codes hc terms hbound regs
    width modulus shape hw hm hshape
  refine ⟨finished rf width modulus (Encoding.encodeList id clauses) shape
    (Encoding.encodeList Encoding.encodeNat (scope (interpretedTerms (clauses := clauses) t d codes terms))),
    primitive_execution program h,?_,?_⟩ <;> rfl

end SubexponentialSAT.SqrtLog.HashScopeProgram.FromTuple

end OAI.Algorithms
