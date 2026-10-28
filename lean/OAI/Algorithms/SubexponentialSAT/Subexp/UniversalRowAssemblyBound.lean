import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceBound
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowWorkspaceBound
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchBound
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryBound

namespace OAI.Algorithms

/-! A uniform polynomial envelope for the actual physical row producer. -/

namespace SubexponentialSAT.Subexp.UniversalRowAssemblyBound

open scoped BigOperators
open BitProgram StructuredCalls
open UniversalRowAssembly

def setupBound (S : ℕ) : ℕ :=
  7 * (S + S + S + S + S + S + S + S + S + S) + S * (7 * S + 14) + 48 * S + 81

def vectorBound (S : ℕ) : ℕ :=
  (7 * S + 5) + 1 +
    (S * (S * MatrixExtendedEntryBound.entryBound S + 6010 * (S + 1)^2 + 44 * S + 8 + 5) + 1) +
    (2 * S + 3) + (3 * (S * (4 * S)) + 3) + 1

def envelope (S : ℕ) : ℕ :=
  setupBound S + vectorBound S +
    (UniversalRowMismatchBound.extractBound S + UniversalRowMismatchBound.mismatchBound S +
      8 * (S * S) + 13) + (7 * S + 5) + (13 * S + 7 * S + 28) +
    UniversalRowWorkspaceBound.rearrangeBound S + UniversalRowSourceBound.sourceBound S +
    (6 * UniversalRowSourceBound.sourceLengthBound S + 6 + UniversalRowWorkspaceBound.cleanupBound S)

/-- A deliberately coarse degree-six polynomial, independent of the row. -/
def uniformBound (S : ℕ) : ℕ := 1000000000000000 * S ^ 6

theorem envelope_le (S : ℕ) (hS : 1 ≤ S) : envelope S ≤ uniformBound S := by
  have h0 : 1 ≤ S^6 := by simpa using Nat.pow_le_pow_right hS (show 0 ≤ 6 by decide)
  have h1 : S ≤ S^6 := by simpa using Nat.pow_le_pow_right hS (show 1 ≤ 6 by decide)
  have h2 : S^2 ≤ S^6 := Nat.pow_le_pow_right hS (by decide)
  have h3 : S^3 ≤ S^6 := Nat.pow_le_pow_right hS (by decide)
  have h4 : S^4 ≤ S^6 := Nat.pow_le_pow_right hS (by decide)
  have h5 : S^5 ≤ S^6 := Nat.pow_le_pow_right hS (by decide)
  unfold envelope uniformBound setupBound vectorBound MatrixExtendedEntryBound.entryBound
    UniversalRowMismatchBound.extractBound UniversalRowMismatchBound.mismatchBound
    UniversalRowWorkspaceBound.rearrangeBound UniversalRowWorkspaceBound.cleanupBound
    UniversalRowSourceBound.sourceBound UniversalRowSourceBound.sourceLengthBound
    UniversalRowSourceBound.dataBound UniversalRowSourceBound.inputBound
    UniversalRowSourceBound.outerLoopBound UniversalRowSourceBound.termBound
    UniversalRowSourceBound.factorLoopBound UniversalRowSourceBound.factorCallbackBound
    UniversalRowSourceBound.rowBytes UniversalRowSourceBound.termBytes
    UniversalRowSourceBound.factorsBytes UniversalRowSourceBound.factorBytes
    UniversalRowSourceBound.indicesBound
  ring_nf
  omega

theorem monotone_uniformBound : Monotone uniformBound := by
  intro S T h
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 6)

variable {r Q Δ : ℕ}
variable (p : ℕ) [Fact p.Prime] (i : Fin Δ)
variable (u y : MulticolorTypes.UniversalType r Q Δ) (xs : List (ZMod p))

theorem vector_budget_le (S : ℕ) (hS : 1 ≤ S) (hr : r ≤ S) (hQ : Q ≤ S)
    (hΔ : Δ ≤ S) (hR : xs.length ≤ S) (hb : MatrixWordEncoding.width p ≤ S) :
    CorrectionVectorProgram.programBudget p i u y xs ≤ vectorBound S := by
  have he : CorrectionVectorProgram.entryAllowance p i u y xs ≤
      S * MatrixExtendedEntryBound.entryBound S := by
    have hq : CorrectionVectorProgram.entryAllowance p i u y xs ≤
        Q * MatrixExtendedEntryBound.entryBound S := by
      rw [CorrectionVectorProgram.entryAllowance]
      calc
        _ ≤ ∑ _ : Fin Q, MatrixExtendedEntryBound.entryBound S :=
          Finset.sum_le_sum fun t (_ : t ∈ (Finset.univ : Finset (Fin Q))) =>
            MatrixExtendedEntryBound.programBudget_le p i t u y xs S hS hr hQ hΔ hR hb
        _ = Q * MatrixExtendedEntryBound.entryBound S := by simp
    exact hq.trans (Nat.mul_le_mul_right _ hQ)
  unfold CorrectionVectorProgram.programBudget CorrectionVectorProgram.loopBound
    CorrectionVectorProgram.coefficientAllowance vectorBound
  gcongr

omit [Fact p.Prime] in
theorem setup_budget_le (a : Data) (S : ℕ)
    (hm : ∀ j ∈ boundInputPorts, (a.stacks j).length ≤ S)
    (hr : r ≤ S) (hQ : Q ≤ S) (hb : MatrixWordEncoding.width p ≤ S) :
    UniversalRowInputSetup.budget a Q r (MatrixWordEncoding.width p) ≤ setupBound S := by
  rw [UniversalRowInputSetup.budget_eq]
  unfold setupBound
  gcongr <;> first | assumption | exact hm _ (by decide)

theorem selected_size_le (S : ℕ) (hQ : Q ≤ S) :
    (selected i u y).length ≤ S ∧ ∀ j ∈ selected i u y, j ≤ S := by
  constructor
  · have h := List.length_filter_le
      (fun j : Fin Q => decide (y.head j ≠ u.slot i j)) (List.finRange Q)
    have hsel : (selected i u y).length ≤ Q := by
      simpa only [selected, MismatchPlanProgram.selectedPositions,
        List.length_map, List.length_finRange] using h
    exact hsel.trans hQ
  · intro j hj
    obtain ⟨k, _, hk⟩ := List.mem_map.mp hj
    exact hk ▸ (Nat.le_of_lt k.isLt).trans hQ

/-- Only actual master-word lengths and parameter sizes enter the bound.
The two staged type words and staged slot may be bounded independently,
so callers can choose one size before any row is selected. -/
theorem executionBound_le (inverse negative : Fin Q → Word)
    (difference : Fin Q → Fin Q → Word) (a : Data)
    (h : PreparedInput p i u y xs inverse negative difference a)
    (S : ℕ) (hS : 1 ≤ S) (hr : r ≤ S) (hQ : Q ≤ S) (hΔ : Δ ≤ S)
    (hR : xs.length ≤ S) (hb : MatrixWordEncoding.width p ≤ S)
    (htype : CollisionProgram.typeWidth r Q Δ ≤ S)
    (hm : ∀ j ∈ boundInputPorts, (a.stacks j).length ≤ S) :
    executionBound p i u y xs (computedTables p i u y xs inverse negative difference) a ≤
      uniformBound S := by
  have hz := hm 131 (by decide)
  have ho := hm 132 (by decide)
  have hn := hm 134 (by decide)
  have hd : (deltaWord u y a).length ≤ S := by
    unfold deltaWord
    split_ifs <;> assumption
  have hpositions := selected_size_le i u y S hQ
  have valid := computedTables_valid p i u y xs inverse negative difference
    (a.stacks 131) (a.stacks 134) (by simp [h.zero]) h.nodeArrayWidth
    h.inverseWidth h.negativeWidth h.differenceWidth
  have hsource := UniversalRowSourceBound.source_bound_le
    (computedTables p i u y xs inverse negative difference) (a.stacks 131) (a.stacks 134)
    (selected i u y) (deltaWord u y a) (List.replicate xs.length true)
    (a.stacks 131) (a.stacks 132) S valid hpositions.1 hpositions.2 hz hn hd
    (by simpa using hR) hz ho
  have hword : (sourceWord p i u y xs (computedTables p i u y xs inverse negative difference) a).length ≤
      UniversalRowSourceBound.sourceLengthBound S := hsource.2
  have hsourceCost := hsource.1
  have hs := setup_budget_le p a S hm hr hQ hb
  have hv := vector_budget_le p i u y xs S hS hr hQ hΔ hR hb
  have he := UniversalRowMismatchBound.extractBudget_le i S hS hQ hr hΔ htype
  have hf := UniversalRowMismatchBound.budget_le Q r S hS hQ hr
  have hQr : Q * r ≤ S * S := Nat.mul_le_mul hQ hr
  have ha := UniversalRowWorkspaceBound.rearrange_cost_le p i u y xs a S hm hr hQ hR hb
  have hc := UniversalRowWorkspaceBound.cleanup_cost_le p i u y xs
    (computedTables p i u y xs inverse negative difference) a S hm hr hQ hR hb
  apply le_trans _ (envelope_le S hS)
  unfold executionBound envelope
  omega

end SubexponentialSAT.Subexp.UniversalRowAssemblyBound

end OAI.Algorithms
