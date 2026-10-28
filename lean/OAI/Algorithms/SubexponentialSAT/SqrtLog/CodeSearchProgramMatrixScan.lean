import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramMatrixCallback
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramRecordSelection

namespace OAI.Algorithms

/-! First-success scan over the physically generated matrix records. The
success flag certifies the exact matrix retained in the output tape. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def hasDistanceFlag {t D : ℕ} (d : ℕ) (Q : Fin t → Fin D → SparseCode.F3) : Bool :=
  @decide (SparseCode.HasDistance Q d) (LocalCode.decidableHasDistance Q d)

def matrixPorts : RecordPrograms.Ports 20 28 where
  tag := 17
  present := 18
  found := 19
  source := 26
  payload := 27
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def MatrixInvariant (t D d : ℕ) (a : MatrixSearchState) : Prop :=
  MatrixReady t D d a ∧ (a.regs 19 = true →
    ∃ Q : Fin t → Fin D → SparseCode.F3,
      SparseCode.HasDistance Q d ∧ a.stacks 18 = matrixFrames Q)

abbrev matrixSearchCommand : Cmd 20 28 := RecordPrograms.iterate matrixPorts matrixCallback

def matrixSearchProgram := compiled matrixSearchCommand 26 18

theorem matrixReady_state {t D d : ℕ} (a : MatrixSearchState) (ha : MatrixReady t D d a)
    (v pr f : Bool) (src payload : List Bool) :
    MatrixReady t D d (RecordPrograms.state matrixPorts a v pr f src payload) := by
  constructor
  · intro i
    have hi26 : (⟨i.val,by omega⟩ : Fin 28) ≠ 26 := by
      intro h; have hv := congrArg Fin.val h; simp only at hv; omega
    have hi27 : (⟨i.val,by omega⟩ : Fin 28) ≠ 27 := by
      intro h; have hv := congrArg Fin.val h; simp only at hv; omega
    simpa [MatrixReady,matrixProject,RecordPrograms.state,matrixPorts,hi26,hi27]
      using ha.work i
  · simpa [matrixProject,RecordPrograms.state,matrixPorts] using ha.rows
  · simpa [matrixProject,RecordPrograms.state,matrixPorts] using ha.distance
  · simpa [matrixProject,RecordPrograms.state,matrixPorts] using ha.source
  · simpa [matrixProject,RecordPrograms.state,matrixPorts] using ha.payload
  · simpa [matrixProject,RecordPrograms.state,matrixPorts] using ha.scratch
  · simpa [matrixProject,RecordPrograms.state,matrixPorts] using ha.words
  · simpa [matrixProject,RecordPrograms.state,matrixPorts] using ha.temporary
  · simpa [matrixProject,RecordPrograms.state,matrixPorts] using ha.oldMatrix

theorem matrixInvariant_reset {t D d : ℕ} (base : MatrixSearchState)
    (hb : MatrixInvariant t D d base) (suffix : List Bool) :
    MatrixInvariant t D d (RecordPrograms.state matrixPorts base false true false suffix []) := by
  refine ⟨matrixReady_state base hb.1 _ _ _ _ _,?_⟩
  simp [RecordPrograms.state,matrixPorts]

theorem matrix_contract (t D d : ℕ) :
    RecordSelection.Contract matrixPorts matrixCallback matrixFrames
      (fun Q : Fin t → Fin D → SparseCode.F3 => hasDistanceFlag d Q)
      (fun _ => candidateBudget t D d + 2) (MatrixInvariant t D d) := by
  intro Q tail base hb
  let a := RecordPrograms.state matrixPorts base false true false tail (matrixFrames Q).reverse
  have ha : MatrixReady t D d a := matrixReady_state base hb.1 _ _ _ _ _
  obtain ⟨n,out,hn,he,hr,hf,h17,h18,h26,h27,hm⟩ := matrixCallback_eval Q a ha (by
    simp [a,RecordPrograms.state,matrixPorts])
  have hs : RecordPrograms.state matrixPorts out false true
      (hasDistanceFlag d Q) tail [] = out := by
    apply RecordPrograms.state_eq_self
    · simpa [a,RecordPrograms.state,matrixPorts] using h17
    · simpa [a,RecordPrograms.state,matrixPorts] using h18
    · exact hf
    · simpa [a,RecordPrograms.state,matrixPorts] using h26
    · exact h27
  refine ⟨n,out,hn,⟨hr,?_⟩,hf,hs.symm ▸ he⟩
  intro htrue
  have hQ : SparseCode.HasDistance Q d := by
    simpa [hasDistanceFlag, hf] using htrue
  exact ⟨Q,hQ,hm⟩

def matrixSearchBudget (t D d : ℕ) :=
  4 + 3 ^ (t * D) * (30 * (t * D) + candidateBudget t D d + 9)

theorem matrix_search_runsIn {t D d : ℕ} (base : MatrixSearchState)
    (hb : MatrixInvariant t D d base)
    (hex : ∃ Q : Fin t → Fin D → SparseCode.F3, SparseCode.HasDistance Q d)
    (v pr f : Bool) :
    ∃ (out : MatrixSearchState) (tail : List Bool)
      (Q : Fin t → Fin D → SparseCode.F3),
      SparseCode.HasDistance Q d ∧ out.stacks 18 = matrixFrames Q ∧
      RunsIn matrixSearchProgram (matrixSearchBudget t D d)
        ((RecordPrograms.state matrixPorts base v pr f
          (ProgramEncoding.encodeRecords (framedCandidates 3 (t * D))) []).withPC
            (some matrixSearchProgram.entry))
        ((RecordPrograms.state matrixPorts out false true true tail []).withPC none) := by
  obtain ⟨values,hvalues,hlen,hcomplete⟩ := generated_matrices_typed t D
  obtain ⟨n,out,hn,hout,hflag,he⟩ := RecordSelection.iterate_run matrixPorts matrixCallback
    matrixFrames (fun Q : Fin t → Fin D → SparseCode.F3 => hasDistanceFlag d Q)
    (fun _ => candidateBudget t D d + 2) (MatrixInvariant t D d)
    (matrix_contract t D d) matrixInvariant_reset values [] base hb v pr f
  have hany : values.any (fun Q : Fin t → Fin D → SparseCode.F3 => hasDistanceFlag d Q) = true := by
    obtain ⟨Q,hQ⟩ := hex
    exact List.any_eq_true.mpr ⟨Q,hcomplete Q,by simpa [hasDistanceFlag] using hQ⟩
  rw [hany] at hflag he
  obtain ⟨Q,hQ,hm⟩ := hout.2 hflag
  refine ⟨out,RecordMappedPrograms.unread matrixFrames
    (fun Q : Fin t → Fin D → SparseCode.F3 => hasDistanceFlag d Q) values [],
    Q,hQ,hm,n+1,?_,?_⟩
  · have hc : RecordMappedPrograms.budget matrixFrames
        (fun _ => candidateBudget t D d + 2) values =
        values.length * (30 * (t * D) + candidateBudget t D d + 9) := by
      generalize values = vs
      induction vs with
      | nil => simp [RecordMappedPrograms.budget]
      | cons Q values ih =>
          simp only [RecordMappedPrograms.budget,matrixFrames_ternary_length,
            List.length_cons,ih]
          ring
    rw [hc,hlen] at hn
    unfold matrixSearchBudget
    omega
  · have hinput : Encoding.encodeList matrixFrames values =
        ProgramEncoding.encodeRecords (framedCandidates 3 (t * D)) := by
      rw [encodeList_map_records,hvalues]
    simpa [matrixSearchProgram,List.append_nil,hinput] using compiled_halt_trace he 26 18

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
