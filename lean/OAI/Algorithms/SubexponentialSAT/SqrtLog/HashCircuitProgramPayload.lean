import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramLookup

namespace OAI.Algorithms

/-! Native unframing of the selected incidence dictionary. A successful literal
lookup returns the actual forward dictionary bits on stack5. The success guard
handles a missing key without invoking a parser on an absent frame. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

abbrev transfer (src dst : Fin 7) : Cmd 6 7 :=
  .call (StackRoutines.transferProgram src dst (0 : Fin 6) 1)
def transferred (d : Data) (src dst : Fin 7) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩

theorem transfer_eval (d : Data) (src dst : Fin 7) (hsd : src ≠ dst) :
    Eval (transfer src dst) (3*(d.stacks src).length+3) d (transferred d src dst) := by
  apply Eval.call
  have h := StackRoutines.transferProgram_trace src dst (0 : Fin 6) 1 hsd (by decide)
    d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  simpa [transferred,StackRoutines.transferResult,StructuredProgram.State.withPC,
    StackRoutines.transferProgram,Nat.add_assoc] using hh

abbrev parsePayload : Cmd 6 7 :=
  liftCommand (.call (parseFrame 5 0)) 5 0 Fin.castSucc Fin.castSucc

abbrev unframeResult : Cmd 6 7 :=
  .ite 4 (.seq parsePayload (transfer 0 5)) (.base .skip)

private theorem parse_after (regs : Fin 5 → Bool) (payload : List Bool) :
    afterFrame (recordState regs [] [] [] [] [] (Encoding.frame payload)) 5 0 payload [] =
      recordState (readRegs regs 0 1 (some false)) payload.reverse [] [] [] [] [] := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp []

private theorem transferred_payload (regs : Fin 5 → Bool) (positive : Bool)
    (payload table : List Bool) :
    transferred (extend (recordState regs payload.reverse [] [] [] [] []) positive table) 0 5 =
      data (readRegs regs 0 1 none) positive [] [] payload table := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [readRegs]
  · funext i; fin_cases i <;>
      simp [StackRoutines.transferStacks]

theorem unframeResult_hit (regs : Fin 5 → Bool) (positive : Bool)
    (payload table : List Bool) (hflag : regs 4 = true) :
    ∃ regs', Eval unframeResult (9*payload.length+9)
      (data regs positive [] [] (Encoding.frame payload) table)
      (data regs' positive [] [] payload table) ∧ regs' 4 = true := by
  have hparse := parseFrame_eval (recordState regs [] [] [] [] [] (Encoding.frame payload))
    5 0 (by decide) payload [] (by simp [])
  rw [parse_after] at hparse
  have hp := eval_liftCommand hparse 5 0 Fin.castSucc Fin.castSucc
    (data regs positive [] [] (Encoding.frame payload) table)
    (Fin.castSucc_injective 5) (Fin.castSucc_injective 6)
  simp only [data,embed_extend] at hp
  let rr := readRegs regs 0 1 (some false)
  have ht := transfer_eval
    (extend (recordState rr payload.reverse [] [] [] [] []) positive table) 0 5 (by decide)
  rw [transferred_payload] at ht
  refine ⟨readRegs rr 0 1 none,?_,?_⟩
  · have he := Eval.ite_true (yes := .seq parsePayload (transfer 0 5))
      (no := (.base .skip : Cmd 6 7)) (show (data regs positive [] [] (Encoding.frame payload) table).regs 4 = true by
        simpa [data,extend,recordState] using hflag) (hp.seq ht)
    convert he using 1 ; simp [] ; omega
  · simpa [rr,readRegs] using hflag

theorem unframeResult_miss (regs : Fin 5 → Bool) (positive : Bool)
    (table : List Bool) (hflag : regs 4 = false) :
    Eval unframeResult 1 (data regs positive [] [] [] table) (data regs positive [] [] [] table) := by
  apply Eval.ite_false
  · simpa [data,extend,recordState] using hflag
  · exact .base (.skip _)

/-- The lookup itself and successful unframing are both fixed native code. -/
abbrev literalDictionary : Cmd 6 7 := .seq literalFetch unframeResult

theorem literalDictionary_hit (regs : Fin 5 → Bool) (old positive : Bool)
    (key payload : List Bool) (entries : List (List Bool × List Bool))
    (hlookup : entries.lookup key = some payload) :
    ∃ n ≤ literalFetchBudget key entries + 9*payload.length+9, ∃ regs',
      Eval literalDictionary n
        (data regs old [] (key ++ [positive]).reverse []
          (Squarefree.Program.lookupRecords entries))
        (data regs' positive [] [] payload (Squarefree.Program.lookupRecords entries)) ∧
      regs' 4 = true := by
  obtain ⟨n,hn,rr,he,hf⟩ := literalFetch_eval regs old positive key entries
  rw [hlookup] at he hf
  have he' : Eval literalFetch n
      (data regs old [] (key ++ [positive]).reverse [] (Squarefree.Program.lookupRecords entries))
      (data rr positive [] [] (Encoding.frame payload) (Squarefree.Program.lookupRecords entries)) := by
    simpa [Squarefree.Program.lookupResult,SubexponentialSAT.Subexp.SelectorProgram.framedResult] using he
  have hf' : rr 4 = true := by simpa using hf
  obtain ⟨r2,hp,hf2⟩ := unframeResult_hit rr positive payload
    (Squarefree.Program.lookupRecords entries) hf'
  exact ⟨n+(9*payload.length+9),by omega,r2,he'.seq hp,hf2⟩

def literalDictionaryProgram := compiled literalDictionary 2 5

theorem literalDictionary_hit_runs (regs : Fin 5 → Bool) (old positive : Bool)
    (key payload : List Bool) (entries : List (List Bool × List Bool))
    (hlookup : entries.lookup key = some payload) :
    ∃ regs', RunsIn literalDictionaryProgram
      (literalFetchBudget key entries + 9*payload.length+10)
      ((data regs old [] (key ++ [positive]).reverse []
        (Squarefree.Program.lookupRecords entries)).withPC (some literalDictionaryProgram.entry))
      ((data regs' positive [] [] payload (Squarefree.Program.lookupRecords entries)).withPC none) ∧
      regs' 4 = true := by
  obtain ⟨n,hn,rr,he,hf⟩ := literalDictionary_hit regs old positive key payload entries hlookup
  exact ⟨rr,⟨n+1,by omega,compiled_halt_trace he 2 5⟩,hf⟩
end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
