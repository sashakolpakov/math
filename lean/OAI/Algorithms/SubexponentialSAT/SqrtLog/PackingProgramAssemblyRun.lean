import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyScore

namespace OAI.Algorithms

/-! Concrete execution of the complete weighted-score producer from memory. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

section Run
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

def runBudget (a : Word r Q) (tail fixed : List (Word r Q))
    (pairs : List (I × I)) (indices : List (V ⊕ E)) (raw : List PairScoreProgram.PlanPair)
    (heads remaining : ℕ) (d : Data) (wi wh : List Bool) : ℕ :=
  let ps := scorePairs ivar factor (a::tail) pairs indices a heads remaining fixed
  PackingIncidenceProgram.runtimeBound indices.length raw.length (a::tail).length (ReadPlan.wordWidth r Q)+
  12*parameterLength d+48+headsBudget d heads fixed (a::tail)+
  500*(2*dataLength d+4)^2+1+Zip.budget wi wh ps+
  6*(ProgramEncoding.encodeRecords (Streams.scores wi wh ps)).length+2*wi.length+2*wh.length+14

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem run_from_memory (a : Word r Q) (tail fixed : List (Word r Q))
    (pairs : List (I × I)) (indices : List (V ⊕ E)) (hi : ∀ x,x∈indices)
    (remaining heads s M : ℕ) (raw : List PairScoreProgram.PlanPair) (d : Data)
    (nb sb mb rb : List Bool)
    (hn : SubexponentialSAT.BinaryArithmetic.toNat nb=heads) (hs : SubexponentialSAT.BinaryArithmetic.toNat sb=s)
    (hmass : SubexponentialSAT.BinaryArithmetic.toNat mb=M) (hr : SubexponentialSAT.BinaryArithmetic.toNat rb=r)
    (hraw : raw.Perm (pairs.map (PackingIncidenceProgram.incidencePair ivar factor indices)))
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (remaining+1) fixed d.stacks)
    (hh : SequentialProgram.HighState
      (environment (ScoreBuilderRawInput.environment 1 (a::tail) indices.length raw) nb sb mb rb) d.stacks)
    (hsize : remaining+1+fixed.length=indices.length) :
    ∃ wi wh : List Bool, SubexponentialSAT.BinaryArithmetic.toNat wi=heads^2*s^2 ∧
      SubexponentialSAT.BinaryArithmetic.toNat wh=8*M^2*r^2 ∧
      wi.length ≤ 2*nb.length+2*sb.length+3 ∧ wh.length ≤ 2*mb.length+2*rb.length+6 ∧
      ∃ t ≤ runBudget ivar factor a tail fixed pairs indices raw heads remaining d wi wh,
      ∃ e : Data, Eval command t d e ∧
        e.stacks 0=ProgramEncoding.encodeRecords ((a::tail).map (fun candidate =>
          UnaryCompare.encode (candidateScore ivar factor (a::tail) pairs indices a heads s M remaining fixed candidate))) ∧
        (∀ j,j≠0→e.stacks j=d.stacks j) := by
  obtain ⟨ti,hti,b,hiRun,hbi,hbf⟩ := incidence_eval ivar factor a tail fixed pairs indices hi remaining raw d
    nb sb mb rb hraw hm hh hsize
  have hd20 : d.stacks 20=nb := by simpa [environment] using hh 20 (by decide)
  have hd21 : d.stacks 21=sb := by simpa [environment] using hh 21 (by decide)
  have hd22 : d.stacks 22=mb := by simpa [environment] using hh 22 (by decide)
  have hd23 : d.stacks 23=rb := by simpa [environment] using hh 23 (by decide)
  have hd30 : d.stacks 30=ProgramEncoding.encodeRecords ((a::tail).map ReadPlan.encodeWord) := by
    simpa [environment,ScoreBuilderRawInput.environment,ScoreBuilderProgram.environment] using hh 30 (by decide)
  have hbready : HeadReady b := by
    intro j hj
    have hs : j∈SequentialProgram.scratchPorts :=
      (show ({1,2,3,4,5,6,7,12,13,14,15,16,17,18} : Finset (Fin 48)) ⊆ SequentialProgram.scratchPorts by decide) hj
    have hj0 : j≠0 := by intro he; subst j; simp at hj
    exact (hbf j hj0).trans (hm.scratch j hs)
  have hbhead : SubexponentialSAT.CounterPrograms.value (b.stacks 20)=heads := by
    rw [hbf _ (by decide),hd20,SubexponentialSAT.CounterPrograms.value_eq_toNat,hn]
  have hbp : (b.stacks 19).length=fixed.length := by rw [hbf _ (by decide)]; exact hm.processed
  have hbw : (b.stacks 10).length=ReadPlan.wordWidth r Q := by
    rw [hbf _ (by decide)]; simpa only [ReadPlan.encodeWord_length] using hm.width
  have hba : b.stacks 8=(fixed.reverse.map ReadPlan.encodeWord).flatten++
      (List.replicate (remaining+1) (ReadPlan.encodeWord a)).flatten := by
    rw [hbf _ (by decide),hm.assignment,List.flatten_append]
  obtain ⟨th,hth,c,hheadRun,hch,hcf⟩ := heads_eval b heads fixed (a::tail) _ hbready hbhead hbp hbw hba
    ((hbf _ (by decide)).trans hd30)
  let ps := scorePairs ivar factor (a::tail) pairs indices a heads remaining fixed
  have hcin : inputPairScores c ps := by
    refine ⟨?_,?_,?_⟩
    · rw [hcf _ (by decide),hbi]
      simp [ps,scorePairs,Zip.firstScores,List.map_map,Function.comp_def,UnaryCompare.encode]
    · rw [hch]
      simp [ps,scorePairs,Zip.secondScores,List.map_map,Function.comp_def,UnaryCompare.encode]
    · intro j hj
      have hj0 : j≠0 := by intro he; subst j; simp at hj
      have hj12 : j≠12 := by intro he; subst j; simp at hj
      rw [hcf j hj12,hbf j hj0]
      exact hm.scratch j ((show ({1,2,3,4,5,6,7,13,14,15,16,17} : Finset (Fin 48)) ⊆ SequentialProgram.scratchPorts by decide) hj)
  obtain ⟨wi,wh,hwi,hwh,hwli,hwlh,tw,htw,e,he,heo,he12,hef⟩ := weightAndMerge_eval c ps hcin
  have hwi' : SubexponentialSAT.BinaryArithmetic.toNat wi=heads^2*s^2 := by
    simpa [hcf,hbf,hd20,hd21,hn,hs] using hwi
  have hwh' : SubexponentialSAT.BinaryArithmetic.toNat wh=8*M^2*r^2 := by
    simpa [hcf,hbf,hd22,hd23,hmass,hr] using hwh
  have hwli' : wi.length ≤ 2*nb.length+2*sb.length+3 := by
    simpa [hcf,hbf,hd20,hd21] using hwli
  have hwlh' : wh.length ≤ 2*mb.length+2*rb.length+6 := by
    simpa [hcf,hbf,hd22,hd23] using hwlh
  have hlen : dataLength c=dataLength d := by
    simp [dataLength,PackingWeightProgram.inputLength,projectState,weightPorts,hcf,hbf]
  have hhb : headsBudget b heads fixed (a::tail)=headsBudget d heads fixed (a::tail) := by
    simp [headsBudget,PackingWeightProgram.Gate.budget,projectState,gatePorts,hbf]
  rw [hlen] at htw
  rw [hhb] at hth
  have hscores : Streams.scores wi wh ps=(a::tail).map (fun candidate =>
      UnaryCompare.encode (candidateScore ivar factor (a::tail) pairs indices a heads s M remaining fixed candidate)) := by
    exact Zip.scores_reduced (a::tail)
      (fun candidate => PackingIncidenceProgram.incidenceNumerator ivar factor (a::tail) pairs indices a remaining (candidate::fixed))
      (overlap heads fixed) wi wh heads s M r hwi' hwh'
  refine ⟨wi,wh,hwi',hwh',hwli',hwlh',ti+(th+tw),?_,e,
    hiRun.seq (hheadRun.seq he),?_,?_⟩
  · have hsum := Nat.add_le_add hti (Nat.add_le_add hth htw)
    simpa [runBudget,ps,Nat.add_assoc] using hsum
  · exact heo.trans (congrArg ProgramEncoding.encodeRecords hscores)
  · intro j hj0
    by_cases hj12 : j=12
    · subst j
      exact he12.trans (hm.scratch 12 (by decide)).symm
    · exact (hef j hj0 hj12).trans ((hcf j hj12).trans (hbf j hj0))

end Run
end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
