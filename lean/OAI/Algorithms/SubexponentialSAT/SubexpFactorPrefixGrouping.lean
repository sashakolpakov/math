import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPrefixSemantics

namespace OAI.Algorithms

/-! The grouping producer recovers the original factor incidence order. -/

namespace SubexponentialSAT.SubexpFactorPrefixProgram

open Subexp.FactorPacketCoordinates (Word Prefix)

theorem regroup_lengths_flatten (pieces : List (List Prefix)) :
    regroup (pieces.map List.length) pieces.flatten = pieces := by
  induction pieces with
  | nil => rfl
  | cons ps pieces ih =>
    simp only [List.map_cons, List.flatten_cons, regroup, List.take_left, List.drop_left, ih]

theorem zipPrefixes_projections (ps : List Prefix) :
    zipPrefixes (ps.map Prefix.origin) (ps.map Prefix.taylor) = ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    cases p
    simpa only [List.map_cons, zipPrefixes, List.zipWith_cons_cons, List.cons.injEq, true_and] using ih

/-- No sorting or deduplication is hidden in the positional grouping. -/
theorem grouped_of_pieces (scopes : List (List ℕ)) (pieces : List (List Prefix))
    (h : scopes.map List.length = pieces.map List.length) :
    grouped scopes (pieces.flatten.map Prefix.origin) (pieces.flatten.map Prefix.taylor) = pieces := by
  unfold grouped
  rw [zipPrefixes_projections, h, regroup_lengths_flatten]

end SubexponentialSAT.SubexpFactorPrefixProgram

end OAI.Algorithms
