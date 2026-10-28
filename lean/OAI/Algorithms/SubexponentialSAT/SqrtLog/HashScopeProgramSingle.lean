import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramFlatten
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramSemantics
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPreparation

namespace OAI.Algorithms

/-! One fixed program turns a physically materialized weighted raw row into
its deduplicated original-variable scope. All constant initialization is paid. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Single
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpChunkRecordMap (Data data tapes regs)
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)

def registers : Fin 3 → Fin 11 := ![8,9,10]
def stackPorts : Fin 6 → Fin 22 := ![19,9,0,1,20,21]
theorem registers_injective : Function.Injective registers := by decide
theorem stackPorts_injective : Function.Injective stackPorts := by decide

abbrev flatten : Cmd 11 22 := .call (ProgramLinking.liftProgram Flatten.program registers stackPorts)

private theorem embed_flatten (v p f v' p' f' : Bool) (ell src oldSrc out oldOut : List Bool) :
    embedState registers stackPorts (data v' p' f' ell oldSrc oldOut [])
      (Extract.data v p f src [] [] [] out []) = data v p f ell src out [] := by
  apply embedState_eq_of_ports _ _ _ _ _ registers_injective stackPorts_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h8 : i ≠ 8 := fun h => hi ⟨0,h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨1,h.symm⟩
    have h10 : i ≠ 10 := fun h => hi ⟨2,h.symm⟩
    simp [data,regs,h8,h9,h10]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h19 : i ≠ 19 := fun h => hi ⟨0,h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨1,h.symm⟩
    have h20 : i ≠ 20 := fun h => hi ⟨4,h.symm⟩
    simp [data,tapes,h19,h9,h20]

def wordTerms (terms : List Term) : List (List Bool × List (List Bool)) :=
  terms.map fun term => (term.1,term.2.map Encoding.encodeNat)

theorem wordTerms_payload (terms : List Term) :
    (wordTerms terms).map Flatten.termPayload = terms.map payload := by
  simp only [wordTerms,List.map_map]
  apply List.map_congr_left
  intro term _
  dsimp [Flatten.termPayload,payload]
  congr 1
  induction term.2 with
  | nil => rfl
  | cons c cs ih => simp [Encoding.encodeList,ih]

theorem wordTerms_merged (terms : List Term) :
    (wordTerms terms).reverse.flatMap Prod.snd = (mergedCodes terms).map Encoding.encodeNat := by
  simp [wordTerms,mergedCodes,← List.map_reverse,List.flatMap_map,List.map_flatMap]

private theorem encode_map {α β : Type*} (enc : β → List Bool) (f : α → β) (xs : List α) :
    Encoding.encodeList enc (xs.map f) = Encoding.encodeList (fun a => enc (f a)) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [Encoding.encodeList,ih]

theorem flatten_eval (terms : List Term) (ell : List Bool) :
    ∃ t ≤ Flatten.cost (terms.map payload),
      Eval flatten t
        (data false false false ell (Encoding.encodeList payload terms) [false] [])
        (data false true false ell [] (Encoding.encodeList Encoding.encodeNat (mergedCodes terms)) []) := by
  have ht := Flatten.term_runsIn (wordTerms terms)
  have hp : Encoding.encodeList Flatten.termPayload (wordTerms terms) =
      Encoding.encodeList payload terms := by
    have h := congrArg (Encoding.encodeList id) (wordTerms_payload terms)
    simpa only [encode_map,id_eq] using h
  rw [wordTerms_payload,wordTerms_merged,hp] at ht
  simp only [encode_map] at ht
  let a := data false false false ell (Encoding.encodeList payload terms) [false] []
  let b := Extract.data false true false [] [] [] []
    (Encoding.encodeList Encoding.encodeNat (mergedCodes terms)) []
  have ha : restrictState registers stackPorts a =
      Extract.data false false false (Encoding.encodeList payload terms) [] [] [] [false] [] := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨t,hn,he⟩ := lifted_call Flatten.program registers stackPorts registers_injective stackPorts_injective
    a b (Flatten.cost (terms.map payload)) (by simpa [ha,b] using ht)
  exact ⟨t,hn,by simpa [a,b,embed_flatten] using he⟩

abbrev restore : Cmd 11 22 := .seq (.call (StackRoutines.transferProgram 20 21 8 9))
  (.call (StackRoutines.transferProgram 21 19 8 9))

theorem restore_eval (ell out : List Bool) :
    Eval restore (6*out.length+6) (data false true false ell [] out [])
      (data false false false ell out [] []) := by
  let a := data false true false ell [] out []
  let b := SubexponentialSAT.SubexpScanPrimitives.afterTransfer a 20 21 8 9
  have h1 := SubexponentialSAT.SubexpScanPrimitives.transfer_eval a 20 21 8 9 (by decide) (by decide)
  have h2 := SubexponentialSAT.SubexpScanPrimitives.transfer_eval b 21 19 8 9 (by decide) (by decide)
  have hl : (b.stacks 21).length = out.length := by
    simp [b,a,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,StackRoutines.transferStacks,data,tapes]
  have he : SubexponentialSAT.SubexpScanPrimitives.afterTransfer b 21 19 8 9 = data false false false ell out [] [] := by
    apply SubexponentialSAT.SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;> simp [b,a,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,data,regs,readRegs]
    · funext i; fin_cases i <;> simp [b,a,SubexponentialSAT.SubexpScanPrimitives.afterTransfer,StackRoutines.transferStacks,data,tapes]
  have hh := h1.seq h2
  rw [hl,he] at hh
  simpa [restore,a,data,tapes,show 3*out.length+3+(3*out.length+3)=6*out.length+6 by omega] using hh

abbrev initializeCmd : Cmd 11 22 := .seq (SubexponentialSAT.Subexp.TupleProgram.pushConst 18 8 true)
  (SubexponentialSAT.Subexp.TupleProgram.pushConst 20 8 false)

theorem initialize_eval (source : List Bool) :
    Eval initializeCmd 4 (data false false false [] source [] [])
      (data false false false [true] source [false] []) := by
  have h := (SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (18 : Fin 22) (8 : Fin 11) true
    (data false false false [] source [] [])).seq
    (SubexponentialSAT.Subexp.TupleProgram.pushConst_eval (20 : Fin 22) (8 : Fin 11) false
      (SubexponentialSAT.Subexp.TupleProgram.pushedState 18 8 true (data false false false [] source [] [])))
  convert h using 1
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext i; fin_cases i <;> simp [data,regs]
  · funext i; fin_cases i <;> simp [data,tapes]

abbrev command : Cmd 11 22 := .seq initializeCmd (.seq flatten (.seq restore SubexpScopeProducer.command))
def program := compiled command 19 19

def cost (terms : List Term) : ℕ :=
  11 + Flatten.cost (terms.map payload) +
    6*(Encoding.encodeList Encoding.encodeNat (mergedCodes terms)).length +
    SubexpScopeProducer.budget [true] (mergedCodes terms)

theorem program_runsIn (terms : List Term) :
    ∃ rf, RunsIn program (cost terms)
      ((data false false false [] (Encoding.encodeList payload terms) [] []).withPC (some program.entry))
      ((⟨rf,tapes [true] (Encoding.encodeList Encoding.encodeNat (scope terms)) [] []⟩ : Data).withPC none) := by
  have hi := initialize_eval (Encoding.encodeList payload terms)
  obtain ⟨nf,hf,hef⟩ := flatten_eval terms [true]
  have hr := restore_eval [true] (Encoding.encodeList Encoding.encodeNat (mergedCodes terms))
  obtain ⟨ns,hs,rf,hes⟩ := SubexpScopeProducer.command_eval [true] (mergedCodes terms) (by decide)
  refine ⟨rf,4+(nf+(6*(Encoding.encodeList Encoding.encodeNat (mergedCodes terms)).length+6+ns))+1,?_,?_⟩
  · unfold cost; omega
  · exact compiled_halt_trace (hi.seq (hef.seq (hr.seq hes))) 19 19

end SubexponentialSAT.SqrtLog.HashScopeProgram.Single

end OAI.Algorithms
