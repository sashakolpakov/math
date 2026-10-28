import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingAlgorithm

namespace OAI.Algorithms

/-! Raw incidence-address plans and the exact runtime active-support filter. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp SubexponentialSAT.SqrtLog.Packing

section Plans
variable {I V E : Type*} [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E)

def incidencePlan (indices : List (V ⊕ E)) (i : I) : List ℕ :=
  [indexCode indices (.inl (ivar i)), indexCode indices (.inr (factor i))]

def incidencePair (indices : List (V ⊕ E)) (pair : I × I) : PlanPair :=
  (incidencePlan ivar factor indices pair.1, incidencePlan ivar factor indices pair.2)

theorem incidencePair_valid (indices : List (V ⊕ E))
    (hindices : ∀ a, a ∈ indices) (pair : I × I) :
    ValidRawPair indices.length (incidencePair ivar factor indices pair) := by
  let _ : BEq (V ⊕ E) := instBEqOfDecidableEq
  have hcode (a : V ⊕ E) : indexCode indices a < indices.length :=
    List.idxOf_lt_length_iff.mpr (hindices a)
  constructor
  · simp [incidencePair, incidencePlan]
  · simp [incidencePair, incidencePlan]
  · intro j hj
    simp only [incidencePair, incidencePlan, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> exact hcode _
  · intro j hj
    simp only [incidencePair, incidencePlan, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl <;> exact hcode _

def rawPairs (indices : List (V ⊕ E)) (incidences : List I) : List PlanPair :=
  (incidences.product incidences).map (incidencePair ivar factor indices)

theorem rawPairs_valid (indices : List (V ⊕ E)) (hindices : ∀ a, a ∈ indices)
    (incidences : List I) :
    ∀ pair ∈ rawPairs ivar factor indices incidences, ValidRawPair indices.length pair := by
  intro pair hpair
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hpair
  exact incidencePair_valid ivar factor indices hindices p

@[simp] theorem rawPairs_length (indices : List (V ⊕ E)) (incidences : List I) :
    (rawPairs ivar factor indices incidences).length = incidences.length^2 := by
  change ((incidences.product incidences).map _).length = _
  rw [List.length_map]
  exact (List.length_product incidences incidences).trans (pow_two _).symm

end Plans

section Support
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E)

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem plan_support {Q : ℕ} (indices : List (V ⊕ E)) (pair : I × I) (j : ℕ) :
    j ∈ (incidencePair ivar factor indices pair).1.reverse ++
      (incidencePair ivar factor indices pair).2 ↔
    j ∈ numberedScoreSupport (Q := Q) ivar factor indices (.inl pair) := by
  rcases pair with ⟨i,l⟩
  simp [incidencePair, incidencePlan, numberedScoreSupport, scoreSupport,
 or_left_comm, or_comm]

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
/-- The runtime cutoff and the mathematical unprocessed suffix coincide,
including repeated addresses caused by shared original-variable heads. -/
theorem remaining_eq_active {Q : ℕ} (indices : List (V ⊕ E))
    (processed n : ℕ) (hsize : n + 1 + processed = indices.length) (pair : I × I) :
    PairPreparationProgram.remaining indices.length processed
      (incidencePair ivar factor indices pair) =
    active (numberedScoreSupport (Q := Q) ivar factor indices (.inl pair))
      (List.range' (processed + 1) n) := by
  unfold PairPreparationProgram.remaining
  rw [ActivePlanProgram.active_range_eq]
  have hn : indices.length - (processed + 1) = n := by omega
  rw [hn]
  unfold active
  congr 1
  funext j
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using plan_support (Q := Q) ivar factor indices pair j

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem selectedPair_eq {Q : ℕ} (indices : List (V ⊕ E))
    (processed n : ℕ) (hsize : n + 1 + processed = indices.length) (pair : I × I) :
    PairPreparationProgram.selectedPair indices.length processed
      (incidencePair ivar factor indices pair) =
    (ReadPlan.completionPlan indices.length
      (active (numberedScoreSupport (Q := Q) ivar factor indices (.inl pair))
        (List.range' (processed + 1) n)) (incidencePlan ivar factor indices pair.1),
     ReadPlan.completionPlan indices.length
      (active (numberedScoreSupport (Q := Q) ivar factor indices (.inl pair))
        (List.range' (processed + 1) n)) (incidencePlan ivar factor indices pair.2)) := by
  unfold PairPreparationProgram.selectedPair
  rw [remaining_eq_active ivar factor indices processed n hsize pair]
  rfl
end Support

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

end OAI.Algorithms
