import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgramLookup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramReset
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPreparation

namespace OAI.Algorithms

/-! Native lookup of the optional original marked clause. Local ports49/50
stage original masters705/706; source14 stages original formula700. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Marked
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)

abbrev Data := State 11 80

def tapes (width modulus master shape out index flag clause ell pay : List Bool) : Fin 80 → List Bool :=
  fun i => if i=1 then width else if i=7 then modulus else if i=14 then master
    else if i=15 then shape else if i=48 then out else if i=49 then index
    else if i=50 then flag else if i=73 then clause else if i=72 then ell
    else if i=47 then pay else []
def data (rf : Fin 11 → Bool) (width modulus master shape out index flag clause ell pay : List Bool) : Data :=
  ⟨rf,tapes width modulus master shape out index flag clause ell pay⟩

theorem embed_tapes {r s : ℕ} (register : Fin r → Fin 11) (stack : Fin s → Fin 80)
    (hs : Function.Injective stack) (frame : Data) (source : State r s) (target : Fin 80 → List Bool)
    (hp : ∀ i, target (stack i)=source.stacks i)
    (hf : ∀ i, (¬∃j,stack j=i) → target i=frame.stacks i) :
    embedState register stack frame source =
      (⟨(embedState register stack frame source).regs,target⟩ : Data) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    by_cases hi : ∃j,stack j=i
    · obtain ⟨j,rfl⟩ := hi
      exact (embedState_stack register stack frame source hs j).trans (hp j).symm
    · exact (embedState_stack_frame register stack frame source i hi).trans (hf i hi).symm

def sourceRegisters : Fin 3 → Fin 11 := ![8,9,10]
def sourceStacks : Fin 6 → Fin 80 := ![14,51,49,52,53,73]
theorem sourceRegisters_injective : Function.Injective sourceRegisters := by decide
theorem sourceStacks_injective : Function.Injective sourceStacks := by decide

abbrev fetch : Cmd 11 80 := .call (ProgramLinking.liftProgram HashInputProgram.Source.fetchProgram sourceRegisters sourceStacks)

theorem fetch_eval (clauses : List (List Bool)) (i : Fin clauses.length) (rf : Fin 11 → Bool)
    (width modulus shape out : List Bool) :
    ∃ n ≤ 23*(Encoding.encodeList id clauses).length+19, ∃ rf',
      Eval fetch n
        (data rf width modulus (Encoding.encodeList id clauses) shape out (Encoding.encodeNat i.val) [] [] [] [])
        (data rf' width modulus (Encoding.encodeList id clauses) shape out [] [] clauses[i.val] [] []) := by
  obtain ⟨flag,ht⟩ := HashInputProgram.Source.fetch_original_runs clauses i (rf 8) (rf 9) (rf 10)
  let a := data rf width modulus (Encoding.encodeList id clauses) shape out (Encoding.encodeNat i.val) [] [] [] []
  let z := HashInputProgram.Source.data false false flag (Encoding.encodeList id clauses) [] [] [] [] clauses[i.val]
  have ha : restrictState sourceRegisters sourceStacks a=
      HashInputProgram.Source.data (rf 8) (rf 9) (rf 10) (Encoding.encodeList id clauses) []
        (Encoding.encodeNat i.val) [] [] [] := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j <;> rfl
  obtain ⟨n,hn,he⟩ := lifted_call HashInputProgram.Source.fetchProgram sourceRegisters sourceStacks
    sourceRegisters_injective sourceStacks_injective a z (23*(Encoding.encodeList id clauses).length+19)
    (by simpa [ha,z] using ht)
  have hz := embed_tapes sourceRegisters sourceStacks sourceStacks_injective a z
    (tapes width modulus (Encoding.encodeList id clauses) shape out [] [] clauses[i.val] [] [])
    (by intro j; fin_cases j <;> rfl)
    (by
      intro j hj
      have h49 : j≠49 := fun h => hj ⟨2,h.symm⟩
      have h73 : j≠73 := fun h => hj ⟨5,h.symm⟩
      simp [a,data,tapes,h49,h73])
  rw [hz] at he
  exact ⟨n,hn,_,he⟩

def scopeStacks (i : Fin 22) : Fin 80 := ⟨54+i.val,by omega⟩
theorem scopeStacks_injective : Function.Injective scopeStacks := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val h
  simp only [scopeStacks] at hh
  omega

abbrev prepareScope : Cmd 11 80 := .seq (SubexponentialSAT.Subexp.TupleProgram.pushConst 72 8 true) Reset.all

theorem prepareScope_eval (rf : Fin 11 → Bool) (width modulus master shape out clause : List Bool) :
    Eval prepareScope 13 (data rf width modulus master shape out [] [] clause [] [])
      (data (fun _ => false) width modulus master shape out [] [] clause [true] []) := by
  have h1 := SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (72 : Fin 80) (8 : Fin 11) true
    (data rf width modulus master shape out [] [] clause [] [])
  have h2 := Reset.all_eval (SubexponentialSAT.Subexp.TupleProgram.pushedState 72 8 true
    (data rf width modulus master shape out [] [] clause [] []))
  convert h1.seq h2 using 1
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · rfl
  · funext j; fin_cases j <;> simp [data,tapes]

abbrev extract : Cmd 11 80 := .call (ProgramLinking.liftProgram SubexpScopeProducer.program id scopeStacks)

theorem extract_eval (codes : List ℕ) (width modulus master shape out : List Bool) :
    ∃ n ≤ SubexpScopeProducer.budget [true] codes+1, ∃ rf,
      Eval extract n
        (data (fun _ => false) width modulus master shape out [] []
          (Encoding.encodeList Encoding.encodeNat codes) [true] [])
        (data rf width modulus master shape out [] []
          (Encoding.encodeList Encoding.encodeNat (SubexpScopeProducer.scope [true] codes)) [true] []) := by
  obtain ⟨rf,ht⟩ := SubexpScopeProducer.program_runsIn [true] codes (by decide)
  let a := data (fun _ => false) width modulus master shape out [] []
    (Encoding.encodeList Encoding.encodeNat codes) [true] []
  let z : State 11 22 := ⟨rf,SubexponentialSAT.SubexpChunkRecordMap.tapes [true]
    (Encoding.encodeList Encoding.encodeNat (SubexpScopeProducer.scope [true] codes)) [] []⟩
  have ha : restrictState id scopeStacks a=SubexponentialSAT.SubexpChunkRecordMap.data false false false [true]
      (Encoding.encodeList Encoding.encodeNat codes) [] [] := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · funext j; fin_cases j <;> rfl
    · funext j; fin_cases j <;> rfl
  obtain ⟨n,hn,he⟩ := lifted_call SubexpScopeProducer.program id scopeStacks Function.injective_id
    scopeStacks_injective a z (SubexpScopeProducer.budget [true] codes+1) (by simpa [ha,z] using ht)
  have hz : embedState id scopeStacks a z=data rf width modulus master shape out [] []
      (Encoding.encodeList Encoding.encodeNat (SubexpScopeProducer.scope [true] codes)) [true] [] := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id scopeStacks_injective
    · intro j; rfl
    · intro j hj; exact False.elim (hj ⟨j,rfl⟩)
    · intro j; fin_cases j <;> rfl
    · intro j hj
      have h73 : j≠73 := fun h => hj ⟨19,h.symm⟩
      simp [a,data,tapes,h73]
  exact ⟨n,hn,rf,by simpa [extract,hz] using he⟩

end SubexponentialSAT.SqrtLog.HashScopeProgram.Marked

end OAI.Algorithms
