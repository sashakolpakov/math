import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramGraphOuterCallback
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramRecordSelection

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def graphOuterPorts : RecordPrograms.Ports 20 40 where
  tag := 17
  present := 18
  found := 19
  source := 38
  payload := 39
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def GraphInvariant (D r q : ℕ) (qbits Dbits : List Bool) (a : GraphOuterState) : Prop :=
  GraphOuterReady D r q qbits Dbits a ∧ (a.regs 19 = true →
    ∃ s : Fin D → Cayley.Cube r, WalshExistence.Good q s ∧ a.stacks 29 = matrixFrames s)

abbrev graphSearchCommand : Cmd 20 40 := RecordPrograms.iterate graphOuterPorts graphOuterCallback

def graphSearchProgram := compiled graphSearchCommand 38 29

theorem graphOuterReady_state {D r q : ℕ} {qbits Dbits : List Bool}
    (a : GraphOuterState) (ha : GraphOuterReady D r q qbits Dbits a)
    (v pr f : Bool) (src payload : List Bool) :
    GraphOuterReady D r q qbits Dbits (RecordPrograms.state graphOuterPorts a v pr f src payload) := by
  constructor
  · intro i
    have h38 : (⟨i.val,by omega⟩ : Fin 40) ≠ 38 := by
      intro h; have h' := congrArg Fin.val h; simp only at h'; omega
    have h39 : (⟨i.val,by omega⟩ : Fin 40) ≠ 39 := by
      intro h; have h' := congrArg Fin.val h; simp only at h'; omega
    simpa [graphOuterProject,RecordPrograms.state,graphOuterPorts,h38,h39] using ha.work i
  · simpa [graphOuterProject,RecordPrograms.state,graphOuterPorts] using ha.rows
  · simpa [graphOuterProject,RecordPrograms.state,graphOuterPorts] using ha.qword
  · simpa [graphOuterProject,RecordPrograms.state,graphOuterPorts] using ha.Dword
  · simpa [graphOuterProject,RecordPrograms.state,graphOuterPorts] using ha.source
  · simpa [graphOuterProject,RecordPrograms.state,graphOuterPorts] using ha.payload
  · simpa [graphOuterProject,RecordPrograms.state,graphOuterPorts] using ha.scratch
  · simpa [graphOuterProject,RecordPrograms.state,graphOuterPorts] using ha.characters
  · simpa [graphOuterProject,RecordPrograms.state,graphOuterPorts] using ha.temporary
  · simpa [graphOuterProject,RecordPrograms.state,graphOuterPorts] using ha.oldMatrix
  · exact ha.qvalue
  · exact ha.Dvalue

theorem graphInvariant_reset {D r q : ℕ} {qbits Dbits : List Bool}
    (base : GraphOuterState) (hb : GraphInvariant D r q qbits Dbits base) (suffix : List Bool) :
    GraphInvariant D r q qbits Dbits
      (RecordPrograms.state graphOuterPorts base false true false suffix []) := by
  refine ⟨graphOuterReady_state base hb.1 _ _ _ _ _,?_⟩
  simp [RecordPrograms.state,graphOuterPorts]

theorem graph_contract (D r q : ℕ) (qbits Dbits : List Bool) :
    RecordSelection.Contract graphOuterPorts graphOuterCallback matrixFrames
      (fun s : Fin D → Cayley.Cube r => decide (WalshExistence.Good q s))
      (fun _ => graphCandidateBudget D r qbits.length Dbits.length + 2)
      (GraphInvariant D r q qbits Dbits) := by
  intro s tail base hb
  let a := RecordPrograms.state graphOuterPorts base false true false tail (matrixFrames s).reverse
  have ha : GraphOuterReady D r q qbits Dbits a := graphOuterReady_state base hb.1 _ _ _ _ _
  obtain ⟨n,out,hn,he,hr,hf,h17,h18,h38,h39,hm⟩ := graphOuterCallback_eval s a ha (by
    simp [a,RecordPrograms.state,graphOuterPorts])
  have hs : RecordPrograms.state graphOuterPorts out false true
      (decide (WalshExistence.Good q s)) tail [] = out := by
    apply RecordPrograms.state_eq_self
    · simpa [a,RecordPrograms.state,graphOuterPorts] using h17
    · simpa [a,RecordPrograms.state,graphOuterPorts] using h18
    · exact hf
    · simpa [a,RecordPrograms.state,graphOuterPorts] using h38
    · exact h39
  refine ⟨n,out,hn,⟨hr,?_⟩,hf,hs.symm ▸ he⟩
  intro htrue
  have hgood : WalshExistence.Good q s := by simpa [hf] using htrue
  exact ⟨s,hgood,hm⟩

def graphSearchBudget (D r qlen Dlen : ℕ) :=
  4 + 2 ^ (D * r) * (30 * (D * r) + graphCandidateBudget D r qlen Dlen + 9)

theorem graph_search_runsIn {D r q : ℕ} {qbits Dbits : List Bool} (base : GraphOuterState)
    (hb : GraphInvariant D r q qbits Dbits base)
    (hex : ∃ s : Fin D → Cayley.Cube r, WalshExistence.Good q s) (v pr f : Bool) :
    ∃ (out : GraphOuterState) (tail : List Bool) (s : Fin D → Cayley.Cube r),
      WalshExistence.Good q s ∧ out.stacks 29 = matrixFrames s ∧
      RunsIn graphSearchProgram (graphSearchBudget D r qbits.length Dbits.length)
        ((RecordPrograms.state graphOuterPorts base v pr f
          (ProgramEncoding.encodeRecords (framedCandidates 2 (D * r))) []).withPC
            (some graphSearchProgram.entry))
        ((RecordPrograms.state graphOuterPorts out false true true tail []).withPC none) := by
  obtain ⟨values,hvalues,hlen,hcomplete⟩ := generated_graphs_typed D r
  obtain ⟨n,out,hn,hout,hflag,he⟩ := RecordSelection.iterate_run graphOuterPorts graphOuterCallback
    matrixFrames (fun s : Fin D → Cayley.Cube r => decide (WalshExistence.Good q s))
    (fun _ => graphCandidateBudget D r qbits.length Dbits.length + 2)
    (GraphInvariant D r q qbits Dbits) (graph_contract D r q qbits Dbits)
    graphInvariant_reset values [] base hb v pr f
  have hany : values.any (fun s => decide (WalshExistence.Good q s)) = true := by
    obtain ⟨s,hs⟩ := hex
    exact List.any_eq_true.mpr ⟨s,hcomplete s,by simpa using hs⟩
  rw [hany] at hflag he
  obtain ⟨s,hs,hm⟩ := hout.2 hflag
  refine ⟨out,RecordMappedPrograms.unread matrixFrames
    (fun s : Fin D → Cayley.Cube r => decide (WalshExistence.Good q s)) values [],
    s,hs,hm,n+1,?_,?_⟩
  · have hc : RecordMappedPrograms.budget matrixFrames
        (fun _ => graphCandidateBudget D r qbits.length Dbits.length + 2) values =
        values.length * (30 * (D * r) + graphCandidateBudget D r qbits.length Dbits.length + 9) := by
      generalize values = vs
      induction vs with
      | nil => simp [RecordMappedPrograms.budget]
      | cons s values ih =>
          simp only [RecordMappedPrograms.budget,matrixFrames_binary_length,List.length_cons,ih]
          ring
    rw [hc,hlen] at hn
    unfold graphSearchBudget
    omega
  · have hinput : Encoding.encodeList matrixFrames values =
        ProgramEncoding.encodeRecords (framedCandidates 2 (D * r)) := by
      rw [encodeList_map_records,hvalues]
    simpa only [graphSearchProgram, List.append_nil, hinput] using compiled_halt_trace he 38 29

/-- The finite existence theorem proves termination of this bit search. It is
not called by the machine and does not determine its enumeration order. -/
theorem graph_search_exists {D r q : ℕ} {qbits Dbits : List Bool}
    (hq : 1 ≤ q) (hsize : r = 0 ∨ 8 * q ^ 2 * (r + 1) ≤ D)
    (base : GraphOuterState) (hb : GraphInvariant D r q qbits Dbits base) (v pr f : Bool) :
    ∃ (out : GraphOuterState) (tail : List Bool) (s : Fin D → Cayley.Cube r),
      WalshExistence.Good q s ∧ out.stacks 29 = matrixFrames s ∧
      RunsIn graphSearchProgram (graphSearchBudget D r qbits.length Dbits.length)
        ((RecordPrograms.state graphOuterPorts base v pr f
          (ProgramEncoding.encodeRecords (framedCandidates 2 (D * r))) []).withPC
            (some graphSearchProgram.entry))
        ((RecordPrograms.state graphOuterPorts out false true true tail []).withPC none) := by
  apply graph_search_runsIn base hb _ v pr f
  refine ⟨WalshExistence.construct r D q,?_⟩
  rcases hsize with rfl | hsize
  · exact (WalshExistence.good_iff_smallWalsh hq _).mpr
      (WalshExistence.construct_smallWalsh_zero_dim D q)
  · exact WalshExistence.construct_good r D q hq hsize

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
