import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramCandidatePrepare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramRecordBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram

namespace OAI.Algorithms

/-! Closed verifier for one matrix candidate. Its bound includes restoring the
candidate, copying the complete word list, all rejected words, and cleanup. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open StructuredProgram (Atom)

structure CandidateReady (t D d : ℕ) (a : CandidateState) : Prop where
  work : ∀ i : Fin 18, a.stacks ⟨i.val,by omega⟩ = []
  rows : a.stacks 19 = List.replicate t true
  distance : a.stacks 20 = List.replicate d true
  source : a.stacks 21 = []
  payload : a.stacks 22 = []
  scratch : a.stacks 23 = []
  words : a.stacks 24 = ProgramEncoding.encodeRecords (framedCandidates 3 D)
  temporary : a.stacks 25 = []
  oldMatrix : (a.stacks 18).length ≤ 5 * (t * D)

theorem CandidateReady.of_stacks_eq {t D d : ℕ} {a b : CandidateState}
    (h : b.stacks = a.stacks) (ha : CandidateReady t D d a) : CandidateReady t D d b := by
  constructor
  · simpa only [h] using ha.work
  · simpa only [h] using ha.rows
  · simpa only [h] using ha.distance
  · simpa only [h] using ha.source
  · simpa only [h] using ha.payload
  · simpa only [h] using ha.scratch
  · simpa only [h] using ha.words
  · simpa only [h] using ha.temporary
  · simpa only [h] using ha.oldMatrix

abbrev candidateCommand : Cmd 16 28 :=
  .seq candidatePrepare <|
  .seq (invoke localScanProgram id candidateLocalStacks) <|
  .seq (.base (.atom (.bnot 15 15))) (clearCmd 21)

def candidateProgram := compiled candidateCommand 27 18

def candidateBudget (t D d : ℕ) :=
  25 * (t * D) + 9 * wordRecordsLength D + 15 + 3 * localVerifierBudget t D d

private theorem small_port_ne {n : ℕ} (i : Fin n) (hn : n ≤ 18) (j : Fin 28)
    (hj : 18 ≤ j.val) : (⟨i.val, by omega⟩ : Fin 28) ≠ j := by
  intro h
  have h' := congrArg Fin.val h
  simp only at h'
  omega

private theorem preparedReady {t D d : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (a : CandidateState) (ha : CandidateReady t D d a)
    (hq : a.stacks 27 = (matrixFrames Q).reverse) :
    LocalReady Q d (project id candidateLocalStacks (candidatePrepared a)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    change (candidatePrepared a).stacks ⟨i.val,by omega⟩ = []
    rw [candidatePrepared_frame a _ (small_port_ne i (by omega) _ (by decide))
      (small_port_ne i (by omega) _ (by decide))
      (small_port_ne i (by omega) _ (by decide))]
    exact ha.work i
  · exact candidatePrepared_matrix Q a hq
  · exact (candidatePrepared_frame a 19 (by decide) (by decide) (by decide)).trans ha.rows
  · exact (candidatePrepared_frame a 20 (by decide) (by decide) (by decide)).trans ha.distance
  · exact (candidatePrepared_frame a 23 (by decide) (by decide) (by decide)).trans ha.scratch

theorem candidate_eval {t D d : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (a : CandidateState) (ha : CandidateReady t D d a)
    (hq : a.stacks 27 = (matrixFrames Q).reverse) :
    ∃ (n : ℕ) (out : CandidateState), n ≤ candidateBudget t D d ∧
      Eval candidateCommand n a out ∧ CandidateReady t D d out ∧
      (out.regs 15 = true ↔ SparseCode.HasDistance Q d) ∧
      out.stacks 18 = matrixFrames Q ∧ out.stacks 27 = [] ∧
      out.stacks 26 = a.stacks 26 := by
  let prepared := candidatePrepared a
  let base := project id candidateLocalStacks prepared
  have hr : LocalReady Q d base := preparedReady Q a ha hq
  have hb21 : base.stacks 21 = ProgramEncoding.encodeRecords (framedCandidates 3 D) :=
    (candidatePrepared_words a ha.source).trans ha.words
  have hb22 : base.stacks 22 = [] :=
    (candidatePrepared_frame a 22 (by decide) (by decide) (by decide)).trans ha.payload
  obtain ⟨localOut,found,tail,hrOut,hspec,nl,hnl,htrace⟩ :=
    local_verifier_runsIn Q d base hr (base.regs 13) (base.regs 14) (base.regs 15)
  have hentry : RecordPrograms.state localPorts base (base.regs 13) (base.regs 14)
      (base.regs 15) (ProgramEncoding.encodeRecords (framedCandidates 3 D)) [] = base :=
    RecordPrograms.state_eq_self _ _ _ _ _ _ _ rfl rfl rfl hb21 hb22
  rw [hentry] at htrace
  let small := RecordPrograms.state localPorts localOut false true found tail []
  let middle := embedState id candidateLocalStacks prepared small
  have hcall := invoke_eval localScanProgram id candidateLocalStacks
    Function.injective_id (Fin.castAdd_injective _ _) prepared small htrace
  let flagged := (Atom.bnot 15 15).eval middle
  let out := clearState 21 flagged
  have htail : tail.length ≤ wordRecordsLength D + nl := by
    have h := Subexp.SequentialProgram.trace_stack_length_le htrace 21
    change tail.length ≤ (base.stacks 21).length + nl at h
    simpa only [hb21, generated_words_length] using h
  have hprep : candidatePrepareCost a ≤ 25 * (t * D) + 7 * wordRecordsLength D + 11 := by
    have hm := ha.oldMatrix
    simp only [candidatePrepareCost,hq,List.length_reverse,matrixFrames_ternary_length,
      ha.words,generated_words_length]
    omega
  have hmid (i : Fin 24) : middle.stacks (candidateLocalStacks i) = small.stacks i :=
    embedState_stack id candidateLocalStacks prepared small (Fin.castAdd_injective _ _) i
  have hframe (i : Fin 28) (hi : 24 ≤ i.val) (h27 : i ≠ 27) : middle.stacks i = a.stacks i := by
    rw [show middle.stacks i = prepared.stacks i from
      embedState_stack_frame _ _ _ _ i (by
        rintro ⟨j,hj⟩
        have hv := congrArg Fin.val hj
        simp [candidateLocalStacks] at hv
        omega)]
    exact candidatePrepared_frame a i
      (by intro h; subst i; omega) (by intro h; subst i; omega) h27
  have h21 : middle.stacks 21 = tail := by
    exact (hmid 21).trans (RecordPrograms.state_source _ _ _ _ _ _ _)
  have hnew (i : Fin 28) (hi : i ≠ 21) : out.stacks i = middle.stacks i := by
    simp [out, flagged, clearState, Atom.eval, Atom.instr, execInstr,
      StructuredProgram.State.ofCfg, hi]
  have hsmallready : LocalReady Q d small := by
    rcases hrOut with ⟨hw,hm,ht,hd,h23⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i
      have hi21 : wordStacks i ≠ (21 : Fin 24) := by
        intro h; have hv := congrArg Fin.val h
        simp [wordStacks] at hv
        omega
      have hi22 : wordStacks i ≠ (22 : Fin 24) := by
        intro h; have hv := congrArg Fin.val h
        simp [wordStacks] at hv
        omega
      simpa [small, RecordPrograms.state, localPorts, hi21, hi22] using hw i
    · simpa [small, RecordPrograms.state, localPorts] using hm
    · simpa [small, RecordPrograms.state, localPorts] using ht
    · simpa [small, RecordPrograms.state, localPorts] using hd
    · simpa [small, RecordPrograms.state, localPorts] using h23
  have hmat : out.stacks 18 = matrixFrames Q :=
    (hnew 18 (by decide)).trans ((hmid 18).trans hsmallready.2.1)
  have h27mid : middle.stacks 27 = prepared.stacks 27 := by
    apply embedState_stack_frame
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    simp [candidateLocalStacks] at hv
    omega
  have hflag : out.regs 15 = !found := by
    change (!middle.regs 15) = (!found)
    have hr15 : middle.regs 15 = small.regs 15 :=
      embedState_register id candidateLocalStacks prepared small Function.injective_id 15
    have hs15 : small.regs 15 = found :=
      RecordPrograms.state_found localPorts localOut false true found tail []
    exact congrArg Bool.not (hr15.trans hs15)
  refine ⟨candidatePrepareCost a + (nl + (1 + (2 * tail.length + 3))), out, ?_, ?_, ?_, ?_, hmat, ?_, ?_⟩
  · unfold candidateBudget
    omega
  · have hc := clear_eval 21 flagged
    have hlen : (flagged.stacks 21).length = tail.length := congrArg List.length h21
    rw [hlen] at hc
    exact (candidatePrepare_eval a ha.temporary).seq
      (hcall.seq ((Eval.base (.atom _ middle)).seq hc))
  · constructor
    · intro i
      rw [hnew _ (small_port_ne i (by omega) _ (by decide))]
      exact (hmid (⟨i.val,by omega⟩ : Fin 24)).trans (hsmallready.1 i)
    · exact (hnew 19 (by decide)).trans ((hmid 19).trans hsmallready.2.2.1)
    · exact (hnew 20 (by decide)).trans ((hmid 20).trans hsmallready.2.2.2.1)
    · simp [out,clearState]
    · exact (hnew 22 (by decide)).trans ((hmid 22).trans (RecordPrograms.state_payload _ _ _ _ _ _ _))
    · exact (hnew 23 (by decide)).trans ((hmid 23).trans hsmallready.2.2.2.2)
    · exact (hnew 24 (by decide)).trans ((hframe 24 (by decide) (by decide)).trans ha.words)
    · exact (hnew 25 (by decide)).trans ((hframe 25 (by decide) (by decide)).trans ha.temporary)
    · rw [hmat,matrixFrames_ternary_length]
  · rw [hflag]
    simpa using hspec
  · exact (hnew 27 (by decide)).trans (h27mid.trans (candidatePrepared_payload a))
  · exact (hnew 26 (by decide)).trans (hframe 26 (by decide) (by decide))

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
