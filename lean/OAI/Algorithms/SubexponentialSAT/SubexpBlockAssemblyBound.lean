import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBlockAssemblyCost

namespace OAI.Algorithms

/-! The enclosing packer pays linearly for its input and output, in addition
to the actual table-source calls. Every factor occurrence is counted. -/

namespace SubexponentialSAT.SubexpBlockAssembly

open SubexpKernelControl (Word)

def factorWork (zero one : Word) (fs : List (List SubexpTableSource.Row)) : ℕ :=
  (fs.map (SubexpTableSource.tableCost zero one)).sum

def termWork (zero one : Word) (t : Term) : ℕ := factorWork zero one t.factors
def groupWork (zero one : Word) (ts : List Term) : ℕ := (ts.map (termWork zero one)).sum
def blockWork (zero one : Word) (b : Block) : ℕ := (b.groups.map (groupWork zero one)).sum
def tableWork (zero one : Word) (bs : List Block) : ℕ := (bs.map (blockWork zero one)).sum

theorem factorProductSteps_le (zero one : Word) (fs : List (List SubexpTableSource.Row)) :
    factorProductSteps zero one fs ≤ factorWork zero one fs +
      10*(Encoding.encodeList SubexpTableSource.encodeRows fs).length +
      10*(factorProduct zero one fs).length := by
  induction fs with
  | nil =>
      simp [factorProductSteps,factorWork,factorProduct,SubexpKernelControl.pushWord_length]
      omega
  | cons f fs ih =>
      simp only [factorProductSteps,factorSteps,factorWork,factorProduct,
        List.map_cons,List.sum_cons,List.flatten_cons,List.length_cons,List.length_append,
        SubexpKernelControl.pushWord_length,SubexpKernelControl.operators_length,
        Encoding.length_encodeList_cons] at *
      omega

theorem termSteps_le (zero one : Word) (t : Term) :
    termSteps zero one t ≤ termWork zero one t + 20*(encodeTerm t).length +
      25*(SubexpKernelControl.encodeTerm (compiledTerm zero one t)).length := by
  have h := factorProductSteps_le zero one t.factors
  simp only [termSteps,termWork,encodeTerm,List.length_append,Encoding.length_frame,
    SubexpKernelControl.encodeTerm,compiledTerm,Encoding.length_encodeList_cons,
    Encoding.length_encodeList_nil,id_eq]
  omega

theorem groupSteps_le (zero one : Word) (ts : List Term) :
    groupSteps zero one ts ≤ groupWork zero one ts + 20*(encodeGroup ts).length +
      30*(SubexpKernelControl.encodeGroup (ts.map (compiledTerm zero one))).length := by
  induction ts with
  | nil => simp [groupSteps,groupWork,encodeGroup,SubexpKernelControl.encodeGroup]
  | cons t ts ih =>
      have ht := termSteps_le zero one t
      simp only [groupSteps,groupWork,encodeGroup,SubexpKernelControl.encodeGroup,
        List.map_cons,List.sum_cons,Encoding.length_encodeList_cons] at *
      omega

theorem groupScan_le (zero one : Word) (gs : List (List Term)) :
    (gs.map (fun ts => 9*(encodeGroup ts).length+groupSteps zero one ts+9)).sum +
        13*(Encoding.encodeList SubexpKernelControl.encodeGroup
          (gs.map (fun ts => ts.map (compiledTerm zero one)))).length ≤
      (gs.map (groupWork zero one)).sum +
        30*(Encoding.encodeList encodeGroup gs).length +
        30*(Encoding.encodeList SubexpKernelControl.encodeGroup
          (gs.map (fun ts => ts.map (compiledTerm zero one)))).length := by
  induction gs with
  | nil => simp
  | cons ts gs ih =>
      have ht := groupSteps_le zero one ts
      simp only [List.map_cons,List.sum_cons,Encoding.length_encodeList_cons] at *
      omega

theorem blockSteps_le (zero one : Word) (b : Block) :
    blockSteps zero one b ≤ blockWork zero one b + 30*(encodeBlock b).length +
      30*(SubexpKernelControl.encodeBlock (compiledBlock zero one b)).length := by
  have h := groupScan_le zero one b.groups
  simp only [blockSteps,blockWork,encodeBlock,List.length_append,Encoding.length_frame,
    SubexpKernelControl.encodeBlock,compiledBlock,Encoding.length_encodeList_cons,
    Encoding.length_encodeList_nil,id_eq]
  omega

/-- The factor-call sum is not hidden in the byte-processing overhead. -/
theorem assemblySteps_le (zero one : Word) (bs : List Block) :
    assemblySteps zero one bs ≤ tableWork zero one bs +
      30*((encodeBlocks bs).length+(assembled zero one bs).length) := by
  induction bs with
  | nil =>
      simp [assemblySteps,tableWork,encodeBlocks,assembled,SubexpKernelControl.encodeBlocks]
  | cons b bs ih =>
      have hb := blockSteps_le zero one b
      simp only [assemblySteps,tableWork,encodeBlocks,assembled,SubexpKernelControl.encodeBlocks,
        List.map_cons,List.sum_cons,Encoding.length_encodeList_cons] at *
      omega

theorem actualProgram_runsIn_linear (zero one : Word) (bs : List Block) :
    BitProgram.RunsIn actualProgram
      (tableWork zero one bs + 30*((encodeBlocks bs).length+(assembled zero one bs).length))
      ((serviceState (encodeBlocks bs) zero one).withPC (some actualProgram.entry))
      ((serviceState (assembled zero one bs) zero one).withPC none) :=
  (actualProgram_runsIn zero one bs).mono (assemblySteps_le zero one bs)

end SubexponentialSAT.SubexpBlockAssembly

end OAI.Algorithms
