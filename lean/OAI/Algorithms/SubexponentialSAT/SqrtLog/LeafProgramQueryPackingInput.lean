import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendOutput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramState
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputStats

namespace OAI.Algorithms

/-! The packing problem is determined by the physically measured query.
In particular its incidence count is the same native mask scan exported by
the frontend, including neutral factors for uncovered low variables. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

noncomputable def packingProblem (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) : PackingCallerProgram.Problem where
  scopes := q.scopeRows
  n := BinaryArithmetic.toNat q.ambient
  mask := q.forward
  mask_le := by simp [LeafQueryFrontend.Query.forward,LeafQueryFrontend.highMask]
  r := (produce (q.input k)).r
  Q := (produce (q.input k)).Q
  s := (produce (q.input k)).epsilonDen
  hr := lt_of_lt_of_le (by decide : 0 < 2) (produce_r_ge_two _)
  hQ := by have h := hg.2.2.2.2.2.2.1; omega
  hs := produce_epsilonDen_pos _ hg.2.2.2.1

theorem packingProblem_incidences (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) : (packingProblem q k hg).incidences=(q.input k).incidences := by
  have h := PackingIncidenceInput.Stats.entries_agree q.scopeRows q.forward 0 q.scopeRows.length
    PackingIncidenceInput.Stats.zero
  simpa [packingProblem,PackingCallerProgram.Problem.incidences,
    PackingIncidenceInput.Semantics.nativeEntries,PackingIncidenceInput.Stats.zero,
    LeafQueryFrontend.totals,LeafStatisticsProgram.zeroTotals,
    LeafQueryFrontend.Query.input,LeafQueryFrontend.numericInput] using h

theorem packing_sources (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hg : Guard (q.input k)) (l : Fin 8 → ℕ)
    (hex : LeafQueryFrontend.Exported (Execute.guardedModel (q.input k) l) a)
    (hscopes : a.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows)
    (hmask : a.stacks 719=q.forward) (hambient : a.stacks 709=q.ambient) :
    PackingCallerProgram.Sources a (packingProblem q k hg) := by
  have hi := LeafQueryFrontend.exported_input_values (q.input k) l a hex
  have hp := LeafQueryFrontend.exported_parameter_values (q.input k) l a hex
  constructor
  · exact hscopes
  · exact hi.1
  · exact hmask
  · exact congrArg BinaryArithmetic.toNat hambient
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2.1
  · rw [packingProblem_incidences]
    exact hi.2.2.1

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
