import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyRun

namespace OAI.Algorithms

/-! Numerical closure for the fixed packing scorer.  Every argument of the
bound is an input size or a numeric weight; no running-time oracle occurs. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

def headBudgetBound (total q wordWidth heads L : ℕ) : ℕ :=
  80*(heads+total+L+1)^2+1+
  (24*total*wordWidth+25*total+13*wordWidth+48)+1+
  (7*(1+(2*wordWidth+2)*q)+5)+16+
  (q*(43*total*wordWidth+20*total+17*wordWidth+66)+22)+
  3*(2*(total*wordWidth+total)+3)

def uniformBudget (total pairs raw q wordWidth heads W L : ℕ) : ℕ :=
  let C := pairs*q^4+total*wordWidth
  10000*31^6*(32*(total+raw+q+wordWidth+1)^2+1)^12*q^4+
  12*L+48+headBudgetBound total q wordWidth heads L+
  500*(2*L+4)^2+1+
  500*(q+1)*(W+1)*(2*L+6+C+1)+
  6*(q*(4*W*C+2)+1)+4*(2*L+6)+14

theorem dataLength_eq_parameterLength (d : Data) : dataLength d=parameterLength d := by
  simp [dataLength,parameterLength,PackingWeightProgram.inputLength,projectState,weightPorts]

theorem headsBudget_le {r Q : ℕ} (d : Data) (heads total : ℕ)
    (fixed alphabet : List (Word r Q))
    (hh : SubexponentialSAT.CounterPrograms.value (d.stacks 20)=heads)
    (hp : (d.stacks 19).length ≤ total) (hf : fixed.length ≤ total)
    (ha : d.stacks 30=ProgramEncoding.encodeRecords (alphabet.map ReadPlan.encodeWord)) :
    headsBudget d heads fixed alphabet ≤
      headBudgetBound total alphabet.length (ReadPlan.wordWidth r Q) heads (parameterLength d) := by
  have hn : (d.stacks 20).length ≤ parameterLength d := by unfold parameterLength; omega
  have hc : headCount heads fixed ≤ total := (headCount_le heads fixed).trans hf
  have hg := PackingWeightProgram.Gate.budget_le (projectState gateRegisters gatePorts d)
  change PackingWeightProgram.Gate.budget (projectState gateRegisters gatePorts d) ≤
    80*(SubexponentialSAT.CounterPrograms.value (d.stacks 20)+(d.stacks 19).length+
      (d.stacks 20).length+1)^2 at hg
  rw [hh] at hg
  have hg' : PackingWeightProgram.Gate.budget (projectState gateRegisters gatePorts d) ≤
      80*(heads+total+parameterLength d+1)^2 := by
    exact hg.trans (by gcongr)
  have ha' : (d.stacks 30).length ≤ 1+(2*ReadPlan.wordWidth r Q+2)*alphabet.length := by
    rw [ha]
    have h := ProgramEncoding.encodeRecords_length_le
      (alphabet.map ReadPlan.encodeWord) (ReadPlan.wordWidth r Q) (by
        intro x hx
        obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hx
        exact (ReadPlan.encodeWord_length w).le)
    simpa using h
  have hb := PackingHeadProgramCandidates.budget_le (headRows heads fixed)
    (alphabet.map ReadPlan.encodeWord) (ReadPlan.wordWidth r Q) (by
      intro x hx
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hx
      exact ReadPlan.encodeWord_length w)
  simp only [List.length_map,headRows_length] at hb
  have hb' : PackingHeadProgramCandidates.budget (headRows heads fixed)
      (alphabet.map ReadPlan.encodeWord) ≤
      alphabet.length*(43*total*ReadPlan.wordWidth r Q+20*total+
        17*ReadPlan.wordWidth r Q+66)+22 := hb.trans (by gcongr)
  unfold headsBudget headBudgetBound PackingPrefixProgram.budget
  gcongr

section Run
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem runBudget_le (a : Word r Q) (tail fixed : List (Word r Q))
    (pairs : List (I × I)) (indices : List (V ⊕ E)) (raw : List PairScoreProgram.PlanPair)
    (heads remaining W : ℕ) (d : Data) (wi wh : List Bool)
    (hh : SubexponentialSAT.CounterPrograms.value (d.stacks 20)=heads)
    (hp : (d.stacks 19).length ≤ indices.length) (hf : fixed.length ≤ indices.length)
    (ha : d.stacks 30=ProgramEncoding.encodeRecords ((a::tail).map ReadPlan.encodeWord))
    (hbi : wi.length ≤ 2*parameterLength d+6) (hbh : wh.length ≤ 2*parameterLength d+6)
    (hi : SubexponentialSAT.CounterPrograms.value wi ≤ W) (hw : SubexponentialSAT.CounterPrograms.value wh ≤ W) :
    runBudget ivar factor a tail fixed pairs indices raw heads remaining d wi wh ≤
      uniformBudget indices.length pairs.length raw.length (a::tail).length
        (ReadPlan.wordWidth r Q) heads W (parameterLength d) := by
  let ps := scorePairs ivar factor (a::tail) pairs indices a heads remaining fixed
  let C := pairs.length*(a::tail).length^4+indices.length*ReadPlan.wordWidth r Q
  have hlen : ps.length=(a::tail).length := by simp [ps,scorePairs]
  have hc : ∀ p∈ps,p.1 ≤ C ∧ p.2 ≤ C := by
    intro p hmem
    obtain ⟨candidate,hcan,rfl⟩ := List.mem_map.mp hmem
    have hinc := PackingIncidenceProgram.incidenceNumerator_le ivar factor
      (a::tail) pairs indices a remaining (candidate::fixed)
    have hov := (overlap_le heads fixed candidate).trans (Nat.mul_le_mul_right _ hf)
    dsimp [C]
    exact ⟨hinc.trans (Nat.le_add_right _ _),hov.trans (Nat.le_add_left _ _)⟩
  have hz := Zip.budget_bound wi wh ps (2*parameterLength d+6) W C hbi hbh hi hw hc
  have ho := Streams.resultBody_length_bound wi wh ps W C hi hw hc
  have ho' : (ProgramEncoding.encodeRecords (Streams.scores wi wh ps)).length ≤
      (a::tail).length*(4*W*C+2)+1 := by
    rw [← Streams.resultBody_records,List.length_append,List.length_singleton]
    simpa only [hlen] using Nat.add_le_add_right ho 1
  have hh' := headsBudget_le d heads indices.length fixed (a::tail) hh hp hf ha
  rw [hlen] at hz
  unfold runBudget uniformBudget
  rw [dataLength_eq_parameterLength]
  change PackingIncidenceProgram.runtimeBound _ _ _ _ + _ + _ + _ + _ + _ +
    Zip.budget wi wh ps + _ + _ + _ + _ ≤ _
  unfold PackingIncidenceProgram.runtimeBound PackingIncidenceProgram.inputBound
    ScoreBuilderBounds.runtimeBound
  dsimp only [C,ps] at *
  simp only [List.length_cons] at *
  omega

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
/-- Direct interface to the two exact weights and four input bit strings
returned by `run_from_memory`. -/
theorem runBudget_weights_le (a : Word r Q) (tail fixed : List (Word r Q))
    (pairs : List (I × I)) (indices : List (V ⊕ E)) (raw : List PairScoreProgram.PlanPair)
    (heads remaining s M : ℕ) (d : Data) (wi wh : List Bool)
    (hh : SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 20)=heads)
    (hp : (d.stacks 19).length ≤ indices.length) (hf : fixed.length ≤ indices.length)
    (ha : d.stacks 30=ProgramEncoding.encodeRecords ((a::tail).map ReadPlan.encodeWord))
    (hbi : wi.length ≤ 2*(d.stacks 20).length+2*(d.stacks 21).length+3)
    (hbh : wh.length ≤ 2*(d.stacks 22).length+2*(d.stacks 23).length+6)
    (hi : SubexponentialSAT.BinaryArithmetic.toNat wi=heads^2*s^2)
    (hw : SubexponentialSAT.BinaryArithmetic.toNat wh=8*M^2*r^2) :
    runBudget ivar factor a tail fixed pairs indices raw heads remaining d wi wh ≤
      uniformBudget indices.length pairs.length raw.length (a::tail).length
        (ReadPlan.wordWidth r Q) heads (heads^2*s^2+8*M^2*r^2) (parameterLength d) := by
  apply runBudget_le ivar factor a tail fixed pairs indices raw heads remaining
    (heads^2*s^2+8*M^2*r^2) d wi wh
  · simpa only [SubexponentialSAT.CounterPrograms.value_eq_toNat] using hh
  · exact hp
  · exact hf
  · exact ha
  · unfold parameterLength
    omega
  · unfold parameterLength
    omega
  · rw [SubexponentialSAT.CounterPrograms.value_eq_toNat,hi]
    exact Nat.le_add_right _ _
  · rw [SubexponentialSAT.CounterPrograms.value_eq_toNat,hw]
    exact Nat.le_add_left _ _

end Run
end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
