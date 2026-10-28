import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyMetadata
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputLoose

namespace OAI.Algorithms

/-! The real incidence scorer with paid parameter parking and restoration. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

abbrev incidence : Cmd 16 48 := .seq park (.seq PackingIncidenceProgram.command unpark)

section Run
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidence_eval (a : Word r Q) (tail fixed : List (Word r Q))
    (pairs : List (I × I)) (indices : List (V ⊕ E)) (hi : ∀ x,x∈indices)
    (remaining : ℕ) (raw : List PairScoreProgram.PlanPair) (d : Data)
    (nb sb mb rb : List Bool)
    (hraw : raw.Perm (pairs.map (PackingIncidenceProgram.incidencePair ivar factor indices)))
    (hm : SequentialProgram.Memory ReadPlan.encodeWord a tail (remaining+1) fixed d.stacks)
    (hh : SequentialProgram.HighState
      (environment (ScoreBuilderRawInput.environment 1 (a::tail) indices.length raw) nb sb mb rb) d.stacks)
    (hsize : remaining+1+fixed.length=indices.length) :
    ∃ t ≤ PackingIncidenceProgram.runtimeBound indices.length raw.length (a::tail).length
        (ReadPlan.wordWidth r Q)+12*parameterLength d+48,
      ∃ e : Data, Eval incidence t d e ∧
        e.stacks 0=ProgramEncoding.encodeRecords ((a::tail).map (fun candidate =>
          UnaryCompare.encode (PackingIncidenceProgram.incidenceNumerator ivar factor
            (a::tail) pairs indices a remaining (candidate::fixed)))) ∧
        (∀ j,j≠0→e.stacks j=d.stacks j) := by
  have hready : parkReady d := by
    intro j hjlo hjhi
    exact hm.scratch j ((show ∀ j : Fin 48,12 ≤ j.val→j.val ≤ 16→j∈SequentialProgram.scratchPorts by decide) j hjlo hjhi)
  have hloose : PackingIncidenceInput.LooseMemory a fixed remaining (parked d) := by
    constructor
    · simpa [parked_stack] using hm.assignment
    · simpa [parked_stack,ReadPlan.encodeWord_length] using hm.width
    · simpa [parked_stack] using hm.processed
    · intro j hj
      have hj12 : j≠12 := by intro he; subst j; omega
      have hj13 : j≠13 := by intro he; subst j; omega
      have hj14 : j≠14 := by intro he; subst j; omega
      have hj15 : j≠15 := by intro he; subst j; omega
      have hj20 : j≠20 := by intro he; subst j; omega
      have hj21 : j≠21 := by intro he; subst j; omega
      have hj22 : j≠22 := by intro he; subst j; omega
      have hj23 : j≠23 := by intro he; subst j; omega
      rw [parked_stack]
      simp only [hj12,hj13,hj14,hj15,hj20,hj21,hj22,hj23,or_self,ite_false]
      exact hm.scratch j ((show ∀ j : Fin 48,j.val < 8→j∈SequentialProgram.scratchPorts by decide) j hj)
  have hhigh : SequentialProgram.HighState
      (ScoreBuilderRawInput.environment 1 (a::tail) indices.length raw) (parked d).stacks := by
    intro j hj
    by_cases hp : j=20 ∨ j=21 ∨ j=22 ∨ j=23
    · rcases hp with rfl|rfl|rfl|rfl <;>
        simp [parked_stack,ScoreBuilderRawInput.environment,ScoreBuilderProgram.environment]
    · have h12 : j ≠ 12 := by intro h; subst j; norm_num at hj
      have h13 : j ≠ 13 := by intro h; subst j; norm_num at hj
      have h14 : j ≠ 14 := by intro h; subst j; norm_num at hj
      have h15 : j ≠ 15 := by intro h; subst j; norm_num at hj
      have h20 : j ≠ 20 := by intro h; subst j; exact hp (Or.inl rfl)
      have h21 : j ≠ 21 := by intro h; subst j; exact hp (Or.inr (Or.inl rfl))
      have h22 : j ≠ 22 := by intro h; subst j; exact hp (Or.inr (Or.inr (Or.inl rfl)))
      have h23 : j ≠ 23 := by intro h; subst j; exact hp (Or.inr (Or.inr (Or.inr rfl)))
      rw [parked_stack]
      simp only [h12,h13,h14,h15,hp,ite_false]
      simpa [environment,h20,h21,h22,h23] using hh j hj
  obtain ⟨ts,hts,b,hb,ho,hf⟩ := PackingIncidenceInput.run_from_memory_loose
    ivar factor a tail fixed pairs indices hi remaining raw (parked d) hraw hloose hhigh hsize
  have hbready : unparkReady b := by
    constructor
    · rw [hf _ (by decide),parked_stack]
      simpa using hready 16 (by decide) (by decide)
    · intro j hjlo hjhi
      rw [hf j (by intro he; subst j; omega),parked_stack]
      have hj : j=20 ∨ j=21 ∨ j=22 ∨ j=23 := by
        exact (show ∀ j : Fin 48,20 ≤ j.val→j.val ≤ 23→j=20∨j=21∨j=22∨j=23 by decide) j hjlo hjhi
      rcases hj with rfl|rfl|rfl|rfl <;> simp
  have hu := unpark_eval b hbready
  have hcost : (b.stacks 12).length+(b.stacks 13).length+
      (b.stacks 14).length+(b.stacks 15).length=parameterLength d := by
    simp [hf,parked_stack,parameterLength]
  have htrace := (park_eval d hready).seq (hb.seq hu)
  refine ⟨_,?_,unparked b,htrace,?_,?_⟩
  · rw [hcost]
    omega
  · simpa [unparked_stack] using ho
  · intro j hj
    have he := congrFun (unpark_after_output d b hready hf) j
    simpa [hj] using he

end Run
end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
