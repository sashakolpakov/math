import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainPacking
import OAI.Algorithms.SubexponentialSAT.SubexpMainAssignment
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingCanonicalSpec

namespace OAI.Algorithms

/-! The concrete assignment-to-packing handoff. The specification is derived
from the actual assignment result and its retained width bytes; neither a
packing result nor a lookup-correctness premise is supplied. -/

namespace SubexponentialSAT.SubexpMainPacking

open BitProgram StructuredCalls SubexpMainProgram Subexp
open SubexpLayoutPorts (Allocation master)

variable {er es D r Q Δ : ℕ} [NeZero r]
variable {alloc : Allocation es} {a b : MainState er es}

noncomputable def specAfterAssignment (hr : 0 < r) (hQ : 0 < Q)
    (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : MulticolorTypes.Word r Q) (tail : List (MulticolorTypes.Word r Q))
    (ha : SubexpMainAssignment.Result alloc a b r Q Δ D scopes hd first tail) :
    PackingExecution.Spec (MulticolorTypes.UniversalType r Q Δ) :=
  PackingCanonicalSpec.specWithWidth hr hQ scopes hd first tail
    (b.stacks (master alloc 4)) ha.width

omit [NeZero r] in
/-- All six producer input words come from the checked assignment result.
The scope stream is the original retained input, and width is preserved
literally rather than reconstructed from its length. -/
theorem input_eq_after_assignment (hr : 0 < r) (hQ : 0 < Q)
    (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : MulticolorTypes.Word r Q) (tail : List (MulticolorTypes.Word r Q))
    (ha : SubexpMainAssignment.Result alloc a b r Q Δ D scopes hd first tail)
    (hs : a.stacks (master alloc 0) = SubexpPlanAlphabetBase.scopeBytes scopes) :
    inputs alloc b = (specAfterAssignment hr hQ scopes hd first tail ha).params.input := by
  have hrows : b.stacks (master alloc 2) =
      (PackingCanonicalSpec.rows scopes hd first tail).flatten := ha.assignment
  have hD := ha.headers 3
  change b.stacks (master alloc 8) = List.replicate D true at hD
  have hΔ := ha.headers 2
  change b.stacks (master alloc 7) = List.replicate Δ true at hΔ
  have hscopeFrame := ha.inputs 4
  change b.stacks (master alloc 0) = a.stacks (master alloc 0) at hscopeFrame
  have hscopes := hscopeFrame.trans hs
  change inputs alloc b =
    (PackingCanonicalSpec.params scopes hd first tail (b.stacks (master alloc 4))).input
  rw [inputs_eq, PackingCanonicalSpec.input_eq, hrows, hD, hΔ, hscopes, ha.alphabet]

omit [NeZero r] in
theorem execution_after_assignment (hr : 0 < r) (hQ : 0 < Q)
    (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : MulticolorTypes.Word r Q) (tail : List (MulticolorTypes.Word r Q))
    (ha : SubexpMainAssignment.Result alloc a b r Q Δ D scopes hd first tail)
    (hs : a.stacks (master alloc 0) = SubexpPlanAlphabetBase.scopeBytes scopes) :
    ∃ n ≤ runtimeBound alloc b (specAfterAssignment hr hQ scopes hd first tail ha), ∃ c,
      Eval (procedure er alloc).invoke n b c ∧
      Result alloc b c (specAfterAssignment hr hQ scopes hd first tail ha) :=
  execution alloc b (specAfterAssignment hr hQ scopes hd first tail ha)
    (input_eq_after_assignment hr hQ scopes hd first tail ha hs)

omit [NeZero r] in
theorem program_runsIn_after_assignment (hr : 0 < r) (hQ : 0 < Q)
    (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : MulticolorTypes.Word r Q) (tail : List (MulticolorTypes.Word r Q))
    (ha : SubexpMainAssignment.Result alloc a b r Q Δ D scopes hd first tail)
    (hs : a.stacks (master alloc 0) = SubexpPlanAlphabetBase.scopeBytes scopes) :
    ∃ c, RunsIn (program er alloc)
      (runtimeBound alloc b (specAfterAssignment hr hQ scopes hd first tail ha))
      (b.withPC (some (program er alloc).entry)) (c.withPC none) ∧
      Result alloc b c (specAfterAssignment hr hQ scopes hd first tail ha) :=
  program_runsIn alloc b (specAfterAssignment hr hQ scopes hd first tail ha)
    (input_eq_after_assignment hr hQ scopes hd first tail ha hs)

omit [NeZero r] in
theorem primitive_runsIn_after_assignment (hr : 0 < r) (hQ : 0 < Q)
    (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (first : MulticolorTypes.Word r Q) (tail : List (MulticolorTypes.Word r Q))
    (ha : SubexpMainAssignment.Result alloc a b r Q Δ D scopes hd first tail)
    (hs : a.stacks (master alloc 0) = SubexpPlanAlphabetBase.scopeBytes scopes) :
    ∃ c, Computation.RunsIn (primitive (program er alloc)).step
      (primitiveOverhead (program er alloc) *
        runtimeBound alloc b (specAfterAssignment hr hQ scopes hd first tail ha))
      (primitiveCfg (program er alloc) (b.withPC (some (program er alloc).entry)))
      (primitiveCfg (program er alloc) (c.withPC none)) ∧
      Result alloc b c (specAfterAssignment hr hQ scopes hd first tail ha) :=
  primitive_runsIn alloc b (specAfterAssignment hr hQ scopes hd first tail ha)
    (input_eq_after_assignment hr hQ scopes hd first tail ha hs)

end SubexponentialSAT.SubexpMainPacking

end OAI.Algorithms
