import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramAssemblyScore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadIncrementalPhysical

namespace OAI.Algorithms

/-! Equality of all candidate comparisons with the original rational score. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp SubexponentialSAT.SqrtLog.Packing

section Ordering
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E) {r Q : ℕ} [NeZero r]

omit [NeZero r] [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem sequentialIncidenceCount_eq (alphabet : List (Word r Q)) (pairs : List (I × I))
    (vertices : List V) (factors : List E) (default : Word r Q) (remaining : ℕ)
    (fixed : List (Word r Q)) :
    PackingHeadIncremental.sequentialIncidenceCount ivar factor alphabet pairs vertices factors default remaining fixed =
      PackingIncidenceProgram.incidenceNumerator ivar factor alphabet pairs
        (headsFirstIndices vertices factors) default remaining fixed := by
  let heads : List (Fin Q × V × V) := (List.finRange Q).flatMap (fun t =>
    (vertices.product vertices).map (fun p => (t,p.1,p.2)))
  have ht : PackingHeadIncremental.headTerms (I:=I) (Q:=Q) vertices = heads.map Sum.inr := by
    simp [PackingHeadIncremental.headTerms,heads,List.map_flatMap,List.map_map,Function.comp_def]
  unfold PackingHeadIncremental.sequentialIncidenceCount PackingIncidenceProgram.incidenceNumerator
  rw [ht,PackingIncidenceProgram.unweightedCounts_split]

omit [NeZero r] in
theorem overlap_eq_physical (headCount : ℕ) (fixed : List (Word r Q)) (candidate : Word r Q) :
    overlap headCount fixed candidate=PackingHeadIncremental.physicalOverlap headCount candidate fixed := by
  rw [overlap_cases]
  rfl

omit [Fintype I] [Fintype E] [DecidableEq I] in
theorem candidateScore_order (alphabet : List (Word r Q)) (haN : alphabet.Nodup)
    (haC : ∀ z,z∈alphabet) (hq : 0 < alphabet.length)
    (pairs : List (I × I)) (vertices : List V) (factors : List E)
    (hvN : vertices.Nodup) (hvC : ∀ v,v∈vertices)
    (w : Weights) (s M : ℕ)
    (hi : w.incidence=vertices.length^2*(s*alphabet.length^2)^2)
    (hh : w.head=M^2*(2*r)^2)
    (default : Word r Q) (remaining : ℕ) (fixed : List (Word r Q))
    (hsize : remaining+1+fixed.length=(headsFirstIndices vertices factors).length)
    (x y : Word r Q) :
    candidateScore ivar factor alphabet pairs (headsFirstIndices vertices factors) default
      vertices.length s M remaining fixed x ≤
    candidateScore ivar factor alphabet pairs (headsFirstIndices vertices factors) default
      vertices.length s M remaining fixed y ↔
    sequentialNumerator ivar factor alphabet
      (pairs.map Sum.inl++PackingHeadIncremental.headTerms (I:=I) (Q:=Q) vertices)
      (headsFirstIndices vertices factors) w default remaining (x::fixed) ≤
    sequentialNumerator ivar factor alphabet
      (pairs.map Sum.inl++PackingHeadIncremental.headTerms (I:=I) (Q:=Q) vertices)
      (headsFirstIndices vertices factors) w default remaining (y::fixed) := by
  rw [PackingHeadIncremental.sequentialNumerator_order_physical ivar factor alphabet haN haC
    pairs vertices factors hvN hvC w default remaining fixed hsize x y]
  rw [hi,hh,sequentialIncidenceCount_eq,sequentialIncidenceCount_eq]
  unfold candidateScore
  rw [← overlap_eq_physical,← overlap_eq_physical]
  exact (reducedScore_scaled_order vertices.length s M r alphabet.length _ _ _ _ hq).symm

end Ordering
end SubexponentialSAT.SqrtLog.PackingProgram.Assembly

end OAI.Algorithms
