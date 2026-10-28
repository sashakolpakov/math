import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyBounds

namespace OAI.Algorithms

/-! The complete fixed producer discharges the sequential controller ABI. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes

def parameterBits (nb sb mb rb : List Bool) : ℕ := nb.length+sb.length+mb.length+rb.length

def magnitude (heads s M r : ℕ) : ℕ := heads^2*s^2+8*M^2*r^2

section Refinement
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem refines (a : Word r Q) (tail : List (Word r Q))
    (pairs : List (I × I)) (indices : List (V ⊕ E)) (hi : ∀ x,x∈indices)
    (heads s M : ℕ) (raw : List PairScoreProgram.PlanPair)
    (nb sb mb rb : List Bool)
    (hn : SubexponentialSAT.BinaryArithmetic.toNat nb=heads) (hs : SubexponentialSAT.BinaryArithmetic.toNat sb=s)
    (hmass : SubexponentialSAT.BinaryArithmetic.toNat mb=M) (hr : SubexponentialSAT.BinaryArithmetic.toNat rb=r)
    (hraw : raw.Perm (pairs.map (PackingIncidenceProgram.incidencePair ivar factor indices))) :
    SequentialProgram.ScoreBuilderRefines ReadPlan.encodeWord a tail
      (evaluate ivar factor (a::tail) pairs indices a heads s M) command
      (uniformBudget indices.length pairs.length raw.length (a::tail).length
        (ReadPlan.wordWidth r Q) heads (magnitude heads s M r) (parameterBits nb sb mb rb))
      indices.length
      (environment (ScoreBuilderRawInput.environment 1 (a::tail) indices.length raw) nb sb mb rb) := by
  intro remaining fixed d hsize hm _ hh
  obtain ⟨wi,wh,hwi,hwh,hwli,hwlh,t,ht,e,he,ho,hf⟩ := run_from_memory ivar factor
    a tail fixed pairs indices hi remaining heads s M raw d nb sb mb rb hn hs hmass hr hraw hm hh hsize
  have hd20 : d.stacks 20=nb := by simpa [environment] using hh 20 (by decide)
  have hd21 : d.stacks 21=sb := by simpa [environment] using hh 21 (by decide)
  have hd22 : d.stacks 22=mb := by simpa [environment] using hh 22 (by decide)
  have hd23 : d.stacks 23=rb := by simpa [environment] using hh 23 (by decide)
  have hL : parameterLength d=parameterBits nb sb mb rb := by
    simp [parameterLength,parameterBits,hd20,hd21,hd22,hd23]
  have hB := runBudget_le ivar factor a tail fixed pairs indices raw heads remaining
    (magnitude heads s M r) d wi wh (by rw [hd20,SubexponentialSAT.CounterPrograms.value_eq_toNat,hn])
    (by rw [hm.processed]; omega) (by omega)
    (by simpa [environment,ScoreBuilderRawInput.environment,ScoreBuilderProgram.environment] using hh 30 (by decide))
    (by rw [hL]; unfold parameterBits; omega)
    (by rw [hL]; unfold parameterBits; omega)
    (by rw [SubexponentialSAT.CounterPrograms.value_eq_toNat,hwi]; exact Nat.le_add_right _ _)
    (by rw [SubexponentialSAT.CounterPrograms.value_eq_toNat,hwh]; exact Nat.le_add_left _ _)
  rw [hL] at hB
  refine ⟨t,ht.trans hB,e,he,?_,?_,?_⟩
  · simpa only [evaluate] using ho
  · intro j _ hj; exact hf j hj
  · intro j hj
    rw [hf j (by intro h; subst j; omega)]
    exact hh j hj

end Refinement
end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
