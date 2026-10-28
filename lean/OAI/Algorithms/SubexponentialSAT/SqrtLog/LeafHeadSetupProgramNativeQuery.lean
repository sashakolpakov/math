import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRankMagnitude
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramIntervalBounds

namespace OAI.Algorithms

/-! Instantiate the closed head setup from the actual frontend query and
native packing output. Structural bounds are derived, not new promises. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp
open PackingCallerProgram LeafParametersProgram

def queryInputs (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (a : Word (LeafProgram.Query.packingProblem q k hg).r (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r (LeafProgram.Query.packingProblem q k hg).Q))
    (t : Fin (LeafProgram.Query.packingProblem q k hg).Q) : Inputs where
  n := (LeafProgram.Query.packingProblem q k hg).n
  N := (LeafProgram.Query.packingProblem q k hg).factors
  r := (LeafProgram.Query.packingProblem q k hg).r
  Q := (LeafProgram.Query.packingProblem q k hg).Q
  D := (LeafProgram.Query.packingProblem q k hg).incidences
  R := (produce (q.input k)).R
  occurrence := (q.input k).occurrence
  packing := ProducedQueryRank.packing (LeafProgram.Query.packingProblem q k hg) a tail
  node := t
  plans := PackingIncidenceInput.Semantics.nativeEntries q.scopeRows q.forward
  rows := ProducedQueryRank.rows (LeafProgram.Query.packingProblem q k hg) a tail
  low := q.forward.map Bool.not
  height := unary (TailInterval.intervalStart (produce (q.input k)).r (produce (q.input k)).Q
    (produce (q.input k)).R)
  width := unary (1+2*(TailInterval.intervalStart (produce (q.input k)).r (produce (q.input k)).Q
    (produce (q.input k)).R)*(produce (q.input k)).R+(produce (q.input k)).Q)
  plans_length := rfl
  rows_length := by simp [ProducedQueryRank.rows,Problem.words_length]
  rows_width := by
    intro row hrow
    obtain ⟨word,_,rfl⟩ := List.mem_map.mp hrow
    simp [ReadPlan.wordWidth]
  height_le := by
    simp only [unary,List.length_replicate]
    exact Interval.intervalStart_le_Q _ _ _ (LeafProgram.Query.packingProblem q k hg).hr
  width_boot := by simp [unary]
  width_node := by simp [unary,LeafProgram.Query.packingProblem]
  fiber_degree := by
    intro v hv
    exact ProducedQueryRank.query_fiber_length_le q k hg ⟨v,hv⟩

@[simp] theorem queryInputs_offset (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (a : Word (LeafProgram.Query.packingProblem q k hg).r (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r (LeafProgram.Query.packingProblem q k hg).Q))
    (t : Fin (LeafProgram.Query.packingProblem q k hg).Q) :
    (queryInputs q k hg a tail t).offset=ProducedQueryRank.queryHeight q k := rfl

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
