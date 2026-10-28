import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramGraphCallback
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramBinaryGenerated
import OAI.Algorithms.SubexponentialSAT.RecordMappedPrograms

namespace OAI.Algorithms

/-! The complete Walsh-character scan. A candidate graph is accepted exactly
when no generated character violates the checked integer inequalities. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def graphPorts : RecordPrograms.Ports 16 36 where
  tag := 13
  present := 14
  found := 15
  source := 33
  payload := 34
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

structure GraphReady {D r : ℕ} (s : Fin D → Cayley.Cube r) (q : ℕ)
    (qbits Dbits : List Bool) (a : GraphSearchState) : Prop where
  work : GraphWorkEmpty a
  matrix : a.stacks 29 = matrixFrames s
  rows : a.stacks 30 = List.replicate D true
  qword : a.stacks 31 = qbits
  Dword : a.stacks 32 = Dbits
  scratch : a.stacks 35 = []
  qvalue : BinaryArithmetic.toNat qbits = q
  Dvalue : BinaryArithmetic.toNat Dbits = D

abbrev graphScanCommand : Cmd 16 36 := RecordPrograms.iterate graphPorts graphWordCallback

def graphScanProgram := compiled graphScanCommand 33 33

theorem graphReady_state {D r : ℕ} {s : Fin D → Cayley.Cube r} {q : ℕ}
    {qbits Dbits : List Bool} (a : GraphSearchState) (ha : GraphReady s q qbits Dbits a)
    (v pr f : Bool) (src payload : List Bool) :
    GraphReady s q qbits Dbits (RecordPrograms.state graphPorts a v pr f src payload) := by
  constructor
  · intro i
    have h33 : graphWordStacks i ≠ (33 : Fin 36) := by
      intro h; have h' := congrArg Fin.val h; simp [graphWordStacks] at h'; omega
    have h34 : graphWordStacks i ≠ (34 : Fin 36) := by
      intro h; have h' := congrArg Fin.val h; simp [graphWordStacks] at h'; omega
    simpa [RecordPrograms.state,graphPorts,h33,h34] using ha.work i
  · simpa [RecordPrograms.state,graphPorts] using ha.matrix
  · simpa [RecordPrograms.state,graphPorts] using ha.rows
  · simpa [RecordPrograms.state,graphPorts] using ha.qword
  · simpa [RecordPrograms.state,graphPorts] using ha.Dword
  · simpa [RecordPrograms.state,graphPorts] using ha.scratch
  · exact ha.qvalue
  · exact ha.Dvalue

theorem graph_word_contract {D r : ℕ} (s : Fin D → Cayley.Cube r) (q : ℕ)
    (qbits Dbits : List Bool) :
    RecordMappedPrograms.Contract graphPorts graphWordCallback
      (fun x => scalarFrames (List.ofFn x)) (fun x => decide (graphWordRejects s x q))
      (fun _ => graphCallbackBudget D r qbits.length Dbits.length) (GraphReady s q qbits Dbits) := by
  intro x tail base hb
  let a := RecordPrograms.state graphPorts base false true false tail
    (scalarFrames (List.ofFn x)).reverse
  have ha : GraphReady s q qbits Dbits a := graphReady_state base hb _ _ _ _ _
  obtain ⟨n,out,hn,he,hemp,hf,h13,h14,h34,hframe⟩ := graphWordCallback_eval s x q qbits Dbits
    ha.qvalue ha.Dvalue a ha.work ha.matrix ha.rows ha.qword ha.Dword ha.scratch (by
      simp [a,RecordPrograms.state,graphPorts])
  have hout : GraphReady s q qbits Dbits out := by
    constructor
    · exact hemp
    · exact (hframe 29 (by decide) (by decide)).trans ha.matrix
    · exact (hframe 30 (by decide) (by decide)).trans ha.rows
    · exact (hframe 31 (by decide) (by decide)).trans ha.qword
    · exact (hframe 32 (by decide) (by decide)).trans ha.Dword
    · exact (hframe 35 (by decide) (by decide)).trans ha.scratch
    · exact ha.qvalue
    · exact ha.Dvalue
  have hstate : RecordPrograms.state graphPorts out false true
      (decide (graphWordRejects s x q)) tail [] = out := by
    apply RecordPrograms.state_eq_self
    · simpa [a,RecordPrograms.state,graphPorts] using h13
    · simpa [a,RecordPrograms.state,graphPorts] using h14
    · exact hf
    · simpa [a,RecordPrograms.state,graphPorts] using hframe 33 (by decide) (by decide)
    · exact h34
  exact ⟨n,out,hn,hout,hstate.symm ▸ he⟩

def graphVerifierBudget (D r qlen Dlen : ℕ) :=
  4 + 2 ^ r * (30 * r + graphCallbackBudget D r qlen Dlen + 7)

theorem graph_verifier_runsIn {D r : ℕ} (s : Fin D → Cayley.Cube r) (q : ℕ)
    (qbits Dbits : List Bool) (base : GraphSearchState) (hb : GraphReady s q qbits Dbits base)
    (v pr f : Bool) :
    ∃ (out : GraphSearchState) (found : Bool) (tail : List Bool),
      GraphReady s q qbits Dbits out ∧ (found = false ↔ WalshExistence.Good q s) ∧
      RunsIn graphScanProgram (graphVerifierBudget D r qbits.length Dbits.length)
        ((RecordPrograms.state graphPorts base v pr f
          (ProgramEncoding.encodeRecords (framedCandidates 2 r)) []).withPC
            (some graphScanProgram.entry))
        ((RecordPrograms.state graphPorts out false true found tail []).withPC none) := by
  obtain ⟨values,hvalues,hlen,hcomplete⟩ := generated_characters_typed r
  obtain ⟨n,out,hn,hout,he⟩ := RecordMappedPrograms.iterate_run graphPorts graphWordCallback
    (fun x => scalarFrames (List.ofFn x)) (fun x => decide (graphWordRejects s x q))
    (fun _ => graphCallbackBudget D r qbits.length Dbits.length) (GraphReady s q qbits Dbits)
    (graph_word_contract s q qbits Dbits) values [] base hb v pr f
  refine ⟨out,values.any (fun x => decide (graphWordRejects s x q)),
    RecordMappedPrograms.unread (fun x => scalarFrames (List.ofFn x))
      (fun x => decide (graphWordRejects s x q)) values [],hout,
    complete_characters_reject_false_iff values hcomplete s q,n+1,?_,?_⟩
  · have hc : RecordMappedPrograms.budget (fun x => scalarFrames (List.ofFn x))
        (fun _ => graphCallbackBudget D r qbits.length Dbits.length) values =
        values.length * (30 * r + graphCallbackBudget D r qbits.length Dbits.length + 7) := by
      generalize values = vs
      induction vs with
      | nil => simp [RecordMappedPrograms.budget]
      | cons x xs ih =>
          simp only [RecordMappedPrograms.budget,scalarFrames_binary_length,
            List.length_ofFn,List.length_cons,ih]
          ring
    rw [hc,hlen] at hn
    unfold graphVerifierBudget
    omega
  · have hinput : Encoding.encodeList (fun x => scalarFrames (List.ofFn x)) values =
        ProgramEncoding.encodeRecords (framedCandidates 2 r) := by
      rw [encodeList_map_records,hvalues]
    simpa only [graphScanProgram, List.append_nil, hinput] using
      compiled_halt_trace he 33 33

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
