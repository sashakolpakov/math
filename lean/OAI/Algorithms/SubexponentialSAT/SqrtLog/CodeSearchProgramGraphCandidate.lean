import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramGraphCandidatePrepare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramGraphRecordBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open StructuredProgram (Atom)

structure GraphCandidateReady (D r q : ℕ) (qbits Dbits : List Bool)
    (a : GraphCandidateState) : Prop where
  work : ∀ i : Fin 29, a.stacks ⟨i.val,by omega⟩ = []
  rows : a.stacks 30 = List.replicate D true
  qword : a.stacks 31 = qbits
  Dword : a.stacks 32 = Dbits
  source : a.stacks 33 = []
  payload : a.stacks 34 = []
  scratch : a.stacks 35 = []
  characters : a.stacks 36 = ProgramEncoding.encodeRecords (framedCandidates 2 r)
  temporary : a.stacks 37 = []
  oldMatrix : (a.stacks 29).length ≤ 5 * (D * r)
  qvalue : BinaryArithmetic.toNat qbits = q
  Dvalue : BinaryArithmetic.toNat Dbits = D

theorem GraphCandidateReady.of_stacks_eq {D r q : ℕ} {qbits Dbits : List Bool}
    {a b : GraphCandidateState} (h : b.stacks = a.stacks)
    (ha : GraphCandidateReady D r q qbits Dbits a) : GraphCandidateReady D r q qbits Dbits b := by
  constructor
  · simpa only [h] using ha.work
  · simpa only [h] using ha.rows
  · simpa only [h] using ha.qword
  · simpa only [h] using ha.Dword
  · simpa only [h] using ha.source
  · simpa only [h] using ha.payload
  · simpa only [h] using ha.scratch
  · simpa only [h] using ha.characters
  · simpa only [h] using ha.temporary
  · simpa only [h] using ha.oldMatrix
  · exact ha.qvalue
  · exact ha.Dvalue

abbrev graphCandidateCommand : Cmd 16 40 :=
  .seq graphCandidatePrepare <|
  .seq (invoke graphScanProgram id graphCandidateStacks) <|
  .seq (.base (.atom (.bnot 15 15))) (clearCmd 33)

def graphCandidateProgram := compiled graphCandidateCommand 39 29

def graphCandidateBudget (D r qlen Dlen : ℕ) :=
  25 * (D * r) + 9 * characterRecordsLength r + 15 + 3 * graphVerifierBudget D r qlen Dlen

private theorem small_port_ne {n : ℕ} (i : Fin n) (hn : n ≤ 29) (j : Fin 40)
    (hj : 29 ≤ j.val) : (⟨i.val,by omega⟩ : Fin 40) ≠ j := by
  intro h
  have h' := congrArg Fin.val h
  simp only at h'
  omega

private theorem graphPreparedReady {D r q : ℕ} {qbits Dbits : List Bool}
    (s : Fin D → Cayley.Cube r) (a : GraphCandidateState)
    (ha : GraphCandidateReady D r q qbits Dbits a)
    (hs : a.stacks 39 = (matrixFrames s).reverse) :
    GraphReady s q qbits Dbits (project id graphCandidateStacks (graphCandidatePrepared a)) := by
  constructor
  · intro i
    change (graphCandidatePrepared a).stacks ⟨i.val,by omega⟩ = []
    rw [graphCandidatePrepared_frame a _ (small_port_ne i (by omega) _ (by decide))
      (small_port_ne i (by omega) _ (by decide)) (small_port_ne i (by omega) _ (by decide))]
    exact ha.work i
  · exact graphCandidatePrepared_matrix s a hs
  · exact (graphCandidatePrepared_frame a 30 (by decide) (by decide) (by decide)).trans ha.rows
  · exact (graphCandidatePrepared_frame a 31 (by decide) (by decide) (by decide)).trans ha.qword
  · exact (graphCandidatePrepared_frame a 32 (by decide) (by decide) (by decide)).trans ha.Dword
  · exact (graphCandidatePrepared_frame a 35 (by decide) (by decide) (by decide)).trans ha.scratch
  · exact ha.qvalue
  · exact ha.Dvalue

theorem graphCandidate_eval {D r q : ℕ} {qbits Dbits : List Bool}
    (s : Fin D → Cayley.Cube r) (a : GraphCandidateState)
    (ha : GraphCandidateReady D r q qbits Dbits a)
    (hs : a.stacks 39 = (matrixFrames s).reverse) :
    ∃ (n : ℕ) (out : GraphCandidateState), n ≤ graphCandidateBudget D r qbits.length Dbits.length ∧
      Eval graphCandidateCommand n a out ∧ GraphCandidateReady D r q qbits Dbits out ∧
      (out.regs 15 = true ↔ WalshExistence.Good q s) ∧
      out.stacks 29 = matrixFrames s ∧ out.stacks 39 = [] ∧ out.stacks 38 = a.stacks 38 := by
  let prepared := graphCandidatePrepared a
  let base := project id graphCandidateStacks prepared
  have hr : GraphReady s q qbits Dbits base := graphPreparedReady s a ha hs
  have hb33 : base.stacks 33 = ProgramEncoding.encodeRecords (framedCandidates 2 r) :=
    (graphCandidatePrepared_words a ha.source).trans ha.characters
  have hb34 : base.stacks 34 = [] :=
    (graphCandidatePrepared_frame a 34 (by decide) (by decide) (by decide)).trans ha.payload
  obtain ⟨localOut,found,tail,hrOut,hspec,nl,hnl,htrace⟩ :=
    graph_verifier_runsIn s q qbits Dbits base hr (base.regs 13) (base.regs 14) (base.regs 15)
  have hentry : RecordPrograms.state graphPorts base (base.regs 13) (base.regs 14)
      (base.regs 15) (ProgramEncoding.encodeRecords (framedCandidates 2 r)) [] = base :=
    RecordPrograms.state_eq_self _ _ _ _ _ _ _ rfl rfl rfl hb33 hb34
  rw [hentry] at htrace
  let small := RecordPrograms.state graphPorts localOut false true found tail []
  let middle := embedState id graphCandidateStacks prepared small
  have hcall := invoke_eval graphScanProgram id graphCandidateStacks
    Function.injective_id (Fin.castAdd_injective _ _) prepared small htrace
  let flagged := (Atom.bnot 15 15).eval middle
  let out := clearState 33 flagged
  have htail : tail.length ≤ characterRecordsLength r + nl := by
    have h := SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le htrace 33
    change tail.length ≤ (base.stacks 33).length + nl at h
    simpa only [hb33, generated_characters_length] using h
  have hprep : graphCandidatePrepareCost a ≤ 25 * (D * r) + 7 * characterRecordsLength r + 11 := by
    have hm := ha.oldMatrix
    simp only [graphCandidatePrepareCost,hs,List.length_reverse,matrixFrames_binary_length,
      ha.characters,generated_characters_length]
    omega
  have hmid (i : Fin 36) : middle.stacks (graphCandidateStacks i) = small.stacks i :=
    embedState_stack id graphCandidateStacks prepared small (Fin.castAdd_injective _ _) i
  have hframe (i : Fin 40) (hi : 36 ≤ i.val) (h39 : i ≠ 39) : middle.stacks i = a.stacks i := by
    rw [show middle.stacks i = prepared.stacks i from embedState_stack_frame _ _ _ _ i (by
      rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      simp [graphCandidateStacks] at hv
      omega)]
    exact graphCandidatePrepared_frame a i
      (by intro h; subst i; omega) (by intro h; subst i; omega) h39
  have h33 : middle.stacks 33 = tail :=
    (hmid 33).trans (RecordPrograms.state_source _ _ _ _ _ _ _)
  have hnew (i : Fin 40) (hi : i ≠ 33) : out.stacks i = middle.stacks i := by
    simp [out,flagged,clearState,Atom.eval,Atom.instr,execInstr,
      StructuredProgram.State.ofCfg,hi]
  have hsmallready : GraphReady s q qbits Dbits small := graphReady_state localOut hrOut _ _ _ _ _
  have hmat : out.stacks 29 = matrixFrames s :=
    (hnew 29 (by decide)).trans ((hmid 29).trans hsmallready.matrix)
  have h39mid : middle.stacks 39 = prepared.stacks 39 := by
    apply embedState_stack_frame
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    simp [graphCandidateStacks] at hv
    omega
  have hflag : out.regs 15 = !found := by
    change (!middle.regs 15) = (!found)
    have hr15 : middle.regs 15 = small.regs 15 :=
      embedState_register id graphCandidateStacks prepared small Function.injective_id 15
    have hs15 : small.regs 15 = found :=
      RecordPrograms.state_found graphPorts localOut false true found tail []
    exact congrArg Bool.not (hr15.trans hs15)
  refine ⟨graphCandidatePrepareCost a + (nl + (1 + (2 * tail.length + 3))),out,?_,?_,?_,?_,hmat,?_,?_⟩
  · unfold graphCandidateBudget; omega
  · have hc := clear_eval 33 flagged
    have hlen : (flagged.stacks 33).length = tail.length := congrArg List.length h33
    rw [hlen] at hc
    exact (graphCandidatePrepare_eval a ha.temporary).seq (hcall.seq ((Eval.base (.atom _ middle)).seq hc))
  · constructor
    · intro i
      rw [hnew _ (small_port_ne i (by omega) _ (by decide))]
      exact (hmid (⟨i.val,by omega⟩ : Fin 36)).trans (hsmallready.work i)
    · exact (hnew 30 (by decide)).trans ((hmid 30).trans hsmallready.rows)
    · exact (hnew 31 (by decide)).trans ((hmid 31).trans hsmallready.qword)
    · exact (hnew 32 (by decide)).trans ((hmid 32).trans hsmallready.Dword)
    · simp [out,clearState]
    · exact (hnew 34 (by decide)).trans ((hmid 34).trans (RecordPrograms.state_payload _ _ _ _ _ _ _))
    · exact (hnew 35 (by decide)).trans ((hmid 35).trans hsmallready.scratch)
    · exact (hnew 36 (by decide)).trans ((hframe 36 (by decide) (by decide)).trans ha.characters)
    · exact (hnew 37 (by decide)).trans ((hframe 37 (by decide) (by decide)).trans ha.temporary)
    · rw [hmat,matrixFrames_binary_length]
    · exact ha.qvalue
    · exact ha.Dvalue
  · rw [hflag]; simpa using hspec
  · exact (hnew 39 (by decide)).trans (h39mid.trans (graphCandidatePrepared_payload a))
  · exact (hnew 38 (by decide)).trans (hframe 38 (by decide) (by decide))

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
