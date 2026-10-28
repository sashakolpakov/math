import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNumericRowSemantics
import OAI.Algorithms.SubexponentialSAT.SubexpMainRowCacheDecoding

namespace OAI.Algorithms

/-!
# The actual source cache at the numeric layout's index type

Only the proof of the node-count equality changes the finite index type.
The stored word lists and their order remain unchanged. All three scalar
laws required by the numeric row theorem follow from the produced cache.
-/

noncomputable section

namespace SubexponentialSAT.SubexpNumericRowCache

open SubexpMainProgram SubexpLayoutPorts SubexpLayoutSpec
open SubexpRowInterpolation

variable {p k Δ r er es : ℕ} {τ : ℚ} [Fact p.Prime] [NeZero r]
variable (c : Parameters p k Δ r τ) (h4 : c.h = 4)
variable {alloc : Allocation es} {a : MainState er es}
variable (h : SubexpMainRowCache.CacheFacts alloc a p)

def index (j : Fin c.Q) : Fin (p ^ 4 - 1) :=
  Fin.cast (Subexp.ComputedMachineSource.nodeCount_eq c h4) j

def inverse (j : Fin c.Q) : List Bool := h.inverse (index c h4 j)

def negative (j : Fin c.Q) : List Bool := h.negative (index c h4 j)

def difference (j l : Fin c.Q) : List Bool :=
  h.difference (index c h4 j) (index c h4 l)

omit [NeZero r] in
theorem inverse_decode (j : Fin c.Q) :
    SubexpRawRow.scalarDecode h.source (inverse c h4 h j) =
      (SubexpNumericRowSemantics.units c h4).nodeInverse j := by
  exact h.inverse_decode (index c h4 j)

omit [NeZero r] in
theorem negative_decode (j : Fin c.Q) :
    SubexpRawRow.scalarDecode h.source (negative c h4 h j) =
      -(SubexpNumericRowSemantics.nodes c h4 j).val := by
  exact h.negative_decode (index c h4 j)

omit [NeZero r] in
theorem difference_decode (j l : Fin c.Q) :
    SubexpRawRow.scalarDecode h.source (difference c h4 h j l) =
      (SubexpNumericRowSemantics.units c h4).differenceInverse j l := by
  have hd := h.difference_decode (index c h4 j) (index c h4 l)
  change SubexpRawRow.scalarDecode h.source (difference c h4 h j l) =
    ((SubexpNumericRowSemantics.nodes c h4 j).val -
      (SubexpNumericRowSemantics.nodes c h4 l).val)⁻¹ at hd
  rw [hd]
  by_cases hjl : j = l
  · subst l
    simp [NodeUnits.differenceInverse]
  · simp only [NodeUnits.differenceInverse, dite_eq_left hjl]
    rfl

private theorem ofFn_cast_eq {X : Type*} {m n : ℕ} (hmn : m = n) (f : Fin n → X) :
    List.ofFn (fun i : Fin m => f (Fin.cast hmn i)) = List.ofFn f := by
  subst n
  rfl

omit [NeZero r] in
/-- Reindexing by the node-count proof does not reorder or rebuild the
actual inverse-word array. -/
theorem inverse_words : List.ofFn (inverse c h4 h) = List.ofFn h.inverse :=
  ofFn_cast_eq (Subexp.ComputedMachineSource.nodeCount_eq c h4) h.inverse

omit [NeZero r] in
theorem negative_words : List.ofFn (negative c h4 h) = List.ofFn h.negative :=
  ofFn_cast_eq (Subexp.ComputedMachineSource.nodeCount_eq c h4) h.negative

omit [NeZero r] in
theorem difference_words :
    List.ofFn (fun j => List.ofFn (difference c h4 h j)) =
      List.ofFn (fun j => List.ofFn (h.difference j)) := by
  unfold difference index
  simp only [ofFn_cast_eq]
  exact ofFn_cast_eq (Subexp.ComputedMachineSource.nodeCount_eq c h4)
    (fun j => List.ofFn (h.difference j))

end SubexponentialSAT.SubexpNumericRowCache

end

end OAI.Algorithms
