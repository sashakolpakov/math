import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgramExtract
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramRecords

namespace OAI.Algorithms

/-! A fixed framed-record fold physically concatenates original literal-code
records after removing each term's coefficient frame. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Flatten
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open Extract (Data data)

def ports : RecordPrograms.Ports 3 6 :=
  ⟨0,1,2,0,1,by decide,by decide,by decide,by decide⟩

def Ready (a : Data) : Prop := a.stacks 2=[] ∧ a.stacks 3=[] ∧ a.stacks 5=[]
def Valid (bits : List Bool) : Prop :=
  ∃ w records, bits = Encoding.frame w ++ Encoding.encodeList id records

theorem parser_state (base : Data) (v p f : Bool) (source payload : List Bool) :
    RecordPrograms.state ports base v p f source payload =
      data v p f source payload (base.stacks 2) (base.stacks 3) (base.stacks 4) (base.stacks 5) := by
  apply SubexponentialSAT.SubexpScanPrimitives.state_ext
  · funext i; fin_cases i <;> simp [RecordPrograms.state,ports,data,ExecCNFRecords.regs]
  · funext i; fin_cases i <;> simp [RecordPrograms.state,ports,data]

theorem contract :
    LeafProgram.FoldContract ports Extract.command (fun a => a.stacks 4) accumulate
      (fun bits => 30*(bits.length+1)) Ready Valid := by
  intro bits tail base hvalid hb
  obtain ⟨w,records,rfl⟩ := hvalid
  obtain ⟨t,ht,he⟩ := Extract.command_eval w tail (base.stacks 4) records
  let b := data false true false tail [] [] [] (recordPrefix records ++ base.stacks 4) []
  refine ⟨t,b,ht,?_,?_,?_⟩
  · simp [Ready,b,data]
  · simp [LeafProgram.foldEffect,b,data]
  · simpa [parser_state,b,data,hb.1,hb.2.1,hb.2.2] using he

abbrev command : Cmd 3 6 := LeafProgram.foldCommand ports Extract.command
abbrev program := compiled command 0 4

def cost (records : List (List Bool)) : ℕ :=
  4 + RecordPrograms.budget (fun bits => 30*(bits.length+1)) records

theorem command_eval (records : List (List Bool)) (out : List Bool)
    (hv : ∀ bits ∈ records, Valid bits) :
    ∃ t ≤ cost records - 1,
      Eval command t (data false false false (Encoding.encodeList id records) [] [] [] out [])
        (data false true false [] [] [] [] (records.foldl (fun o b => accumulate b o) out) []) := by
  let base := data false false false [] [] [] [] out []
  obtain ⟨t,b,ht,hb,hout,he⟩ := LeafProgram.foldCommand_run ports Extract.command
    (fun a => a.stacks 4) accumulate (fun bits => 30*(bits.length+1)) Ready Valid contract
    records [] base hv (by simp [Ready,base,data]) false false false
  refine ⟨t,by unfold cost; omega,?_⟩
  simpa [command,parser_state,base,data,hb.1,hb.2.1,hb.2.2,hout] using he

theorem program_runsIn (records : List (List Bool)) (out : List Bool)
    (hv : ∀ bits ∈ records, Valid bits) :
    RunsIn program (cost records)
      ((data false false false (Encoding.encodeList id records) [] [] [] out []).withPC (some program.entry))
      ((data false true false [] [] [] [] (records.foldl (fun o b => accumulate b o) out) []).withPC none) := by
  obtain ⟨t,ht,he⟩ := command_eval records out hv
  refine ⟨t+1,?_,compiled_halt_trace he 0 4⟩
  have hpos : 1 ≤ cost records := by unfold cost; omega
  omega

def termPayload (term : List Bool × List (List Bool)) : List Bool :=
  Encoding.frame term.1 ++ Encoding.encodeList id term.2

theorem fold_accumulate (terms : List (List Bool × List (List Bool))) (acc : List (List Bool)) :
    (terms.map termPayload).foldl (fun o b => accumulate b o) (Encoding.encodeList id acc) =
      Encoding.encodeList id (terms.reverse.flatMap Prod.snd ++ acc) := by
  induction terms generalizing acc with
  | nil => simp
  | cons term terms ih =>
      rcases term with ⟨w,records⟩
      simp only [List.map_cons,List.foldl_cons,termPayload,accumulate_payload,prefix_encodeRecords]
      rw [ih]
      simp [List.flatMap_append,List.append_assoc]

theorem term_runsIn (terms : List (List Bool × List (List Bool))) :
    RunsIn program (cost (terms.map termPayload))
      ((data false false false (Encoding.encodeList termPayload terms) [] [] [] [false] []).withPC (some program.entry))
      ((data false true false [] [] [] []
        (Encoding.encodeList id (terms.reverse.flatMap Prod.snd)) []).withPC none) := by
  have hm : Encoding.encodeList id (terms.map termPayload) = Encoding.encodeList termPayload terms := by
    induction terms with
    | nil => rfl
    | cons term terms ih => simp [Encoding.encodeList,ih]
  have hv : ∀ bits ∈ terms.map termPayload, Valid bits := by
    intro bits hb
    obtain ⟨term,ht,rfl⟩ := List.mem_map.mp hb
    exact ⟨term.1,term.2,rfl⟩
  have h := program_runsIn (terms.map termPayload) (Encoding.encodeList id ([] : List (List Bool))) hv
  rw [fold_accumulate] at h
  simpa [hm, Encoding.encodeList] using h

theorem cost_le (records : List (List Bool)) :
    cost records ≤ 40*(Encoding.encodeList id records).length := by
  unfold cost
  induction records with
  | nil => simp [RecordPrograms.budget,Encoding.encodeList]
  | cons x xs ih =>
      simp only [RecordPrograms.budget,Encoding.encodeList,List.length_cons,List.length_append,
        Encoding.length_frame,id_eq] at ih ⊢
      omega

end SubexponentialSAT.SqrtLog.HashScopeProgram.Flatten

end OAI.Algorithms
