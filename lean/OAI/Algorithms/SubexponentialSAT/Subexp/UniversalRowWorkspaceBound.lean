import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowAssemblyCost

namespace OAI.Algorithms

/-! Concrete bounds for the fixed universal-row rearrangement and cleanup.

The bounds use only lengths of the sixteen persistent input words and the
actual row parameters.  Cleanup is independent of the generated source:
that word has already been moved outside the workspace being cleared.
-/

namespace SubexponentialSAT.Subexp.UniversalRowWorkspaceBound

open BitProgram StructuredCalls StackRoutines
open UniversalRowWorkspace (Data Word port port_injective)

/-- A deliberately coarse bound for the fixed 23-action rearrangement. -/
def rearrangeBound (S : ℕ) : ℕ := 2 ^ 40 * (S + 1) ^ 2

/-- The same quadratic also bounds clearing all 49 workspace stacks. -/
def cleanupBound (S : ℕ) : ℕ := 2 ^ 40 * (S + 1) ^ 2

private def active (j : Fin 288) : Prop :=
  (∃ k, port k = j) ∨ j ∈ UniversalRowAssembly.boundInputPorts

private def small (L : ℕ) (s : Fin 288 → Word) : Prop :=
  ∀ j, active j → (s j).length ≤ L

private theorem active_port (j : Fin 49) : active (port j) := Or.inl ⟨j, rfl⟩

private theorem active_master (j : Fin 288)
    (h : j ∈ UniversalRowAssembly.boundInputPorts) : active j := Or.inr h

private theorem master_disjoint (j : Fin 288)
    (hj : j ∈ UniversalRowAssembly.boundInputPorts) : ¬ ∃ k, port k = j := by
  have hhigh : 128 ≤ j.val := by
    simp only [UniversalRowAssembly.boundInputPorts, List.mem_cons,
      List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  rintro ⟨k, rfl⟩
  have := UniversalRowWorkspace.port_lt_cache k
  omega

private theorem small_mono {L M : ℕ} {s : Fin 288 → Word}
    (h : small L s) (hLM : L ≤ M) : small M s :=
  fun j hj => (h j hj).trans hLM

private theorem small_update {L : ℕ} {s : Fin 288 → Word}
    (h : small L s) (j : Fin 288) (w : Word) (hw : w.length ≤ L) :
    small L (Function.update s j w) := by
  intro k hk
  by_cases hkj : k = j
  · subst k
    simpa using hw
  · simpa [hkj] using h k hk

private theorem update_length_le {ι : Type*} [DecidableEq ι]
    {L : ℕ} {s : ι → Word} (h : ∀ j, (s j).length ≤ L)
    (j : ι) (w : Word) (hw : w.length ≤ L) :
    ∀ k, (Function.update s j w k).length ≤ L := by
  intro k
  by_cases hkj : k = j
  · subst k
    simpa using hw
  · simpa [hkj] using h k

private def inputPort : UniversalRowRearrange.Action → Fin 288
  | .copy src _ => src
  | .clear dst => port dst

private theorem operation_inputs :
    ∀ op ∈ UniversalRowRearrange.operations, active (inputPort op) := by
  intro op hop
  simp only [UniversalRowRearrange.operations, List.mem_cons,
    List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact active_port _ | exact active_master _ (by decide)

private theorem action_small (op : UniversalRowRearrange.Action) (a : Data) (L : ℕ)
    (ha : small L a.stacks) (hop : active (inputPort op)) :
    small (2 * L) (UniversalRowRearrange.actionResult op a).stacks := by
  have hmono : small (2 * L) a.stacks := small_mono ha (by omega)
  cases op with
  | copy src dst =>
      apply small_update hmono
      have hs := ha src hop
      have hd := ha (port dst) (active_port dst)
      simp only [List.length_append]
      omega
  | clear dst =>
      exact small_update hmono (port dst) [] (by simp)

private theorem action_cost_le (op : UniversalRowRearrange.Action) (a : Data) (L : ℕ)
    (ha : small L a.stacks) (hop : active (inputPort op)) :
    UniversalRowRearrange.actionCost op a ≤ 7 * L + 5 := by
  have hi := ha (inputPort op) hop
  cases op <;> simp only [inputPort] at hi <;>
    simp only [UniversalRowRearrange.actionCost] <;> omega

private theorem result_small (os : List UniversalRowRearrange.Action) (a : Data) (L : ℕ)
    (ha : small L a.stacks) (hos : ∀ op ∈ os, active (inputPort op)) :
    small (2 ^ os.length * L) (UniversalRowRearrange.result os a).stacks := by
  induction os generalizing a L with
  | nil => simpa [UniversalRowRearrange.result] using ha
  | cons op os ih =>
      have ht := ih (UniversalRowRearrange.actionResult op a) (2 * L)
        (action_small op a L ha (hos op (by simp)))
        (fun c hc => hos c (by simp [hc]))
      simpa only [UniversalRowRearrange.result, List.length_cons, pow_succ,
        Nat.mul_assoc] using ht

private theorem cost_potential (os : List UniversalRowRearrange.Action) (a : Data) (L : ℕ)
    (ha : small L a.stacks) (hos : ∀ op ∈ os, active (inputPort op)) :
    UniversalRowRearrange.cost os a + 7 * L ≤
      7 * (2 ^ os.length * L) + 5 * os.length := by
  induction os generalizing a L with
  | nil => simp [UniversalRowRearrange.cost]
  | cons op os ih =>
      have hc := action_cost_le op a L ha (hos op (by simp))
      have ht := ih (UniversalRowRearrange.actionResult op a) (2 * L)
        (action_small op a L ha (hos op (by simp)))
        (fun c hmem => hos c (by simp [hmem]))
      simp only [UniversalRowRearrange.cost, List.length_cons]
      calc
        UniversalRowRearrange.actionCost op a +
            UniversalRowRearrange.cost os (UniversalRowRearrange.actionResult op a) + 7 * L
            ≤ (7 * L + 5) +
              UniversalRowRearrange.cost os (UniversalRowRearrange.actionResult op a) + 7 * L := by omega
        _ = (UniversalRowRearrange.cost os (UniversalRowRearrange.actionResult op a) +
            7 * (2 * L)) + 5 := by ring
        _ ≤ (7 * (2 ^ os.length * (2 * L)) + 5 * os.length) + 5 := by omega
        _ = 7 * (2 ^ (os.length + 1) * L) + 5 * (os.length + 1) := by
          rw [pow_succ]
          ring

private theorem square_arithmetic (S : ℕ) :
    1 ≤ (S + 1) ^ 2 ∧ S ≤ (S + 1) ^ 2 ∧ S * S ≤ (S + 1) ^ 2 ∧
      1 + (2 * S + 2) * S ≤ 8 * (S + 1) ^ 2 := by
  simp only [pow_two]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem source_mem (j : Fin 49) :
    UniversalRowInputSetup.source j ∈ UniversalRowAssembly.boundInputPorts := by
  unfold UniversalRowInputSetup.source
  split_ifs <;> decide

private theorem input_length_le (a : Data) (Q r R b S : ℕ)
    (hm : ∀ j ∈ UniversalRowAssembly.boundInputPorts, (a.stacks j).length ≤ S)
    (hQ : Q ≤ S) (hr : r ≤ S) (hR : R ≤ S) (hb : b ≤ S) :
    ∀ j, (UniversalRowInputSetup.inputStacks a Q r R b j).length ≤ (S + 1) ^ 2 := by
  have hs := (square_arithmetic S).2.1
  have hprod : Q * r ≤ (S + 1) ^ 2 :=
    (Nat.mul_le_mul hQ hr).trans (square_arithmetic S).2.2.1
  have hseed : ∀ j, (UniversalRowInputSetup.seedNative a j).length ≤ (S + 1) ^ 2 := by
    intro j
    unfold UniversalRowInputSetup.seedNative
    split_ifs
    · exact (hm _ (source_mem j)).trans hs
    · simp
  unfold UniversalRowInputSetup.inputStacks
  apply update_length_le
  · apply update_length_le
    · apply update_length_le hseed
      simpa using hR.trans hs
    · simpa using hb.trans hs
  · simpa using hprod

/-- Encoding selected mismatch positions produces a quadratic-size word. -/
theorem indices_length_le {Q : ℕ} (positions : List ℕ)
    (hlen : positions.length ≤ Q) (hmem : ∀ j ∈ positions, j ≤ Q) :
    (UniversalRowTermProgram.indices positions).length ≤ 1 + (2 * Q + 2) * Q := by
  have h := Encoding.length_encodeList_upper id
    (positions.reverse.map UniversalRowFactorLoop.indexWord) Q (by
      intro w hw
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
      simpa using hmem j (List.mem_reverse.mp hj))
  simp only [List.length_map, List.length_reverse] at h
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hlen) _)

variable {r Q Δ : ℕ}
variable (p : ℕ) [Fact p.Prime] (i : Fin Δ)
variable (u y : MulticolorTypes.UniversalType r Q Δ) (xs : List (ZMod p))

theorem selected_indices_length_le :
    (UniversalRowTermProgram.indices (UniversalRowAssembly.selected i u y)).length ≤
      1 + (2 * Q + 2) * Q := by
  apply indices_length_le
  · simpa only [UniversalRowAssembly.selected, MismatchPlanProgram.selectedPositions,
      List.length_map, List.length_finRange] using
      List.length_filter_le (fun j : Fin Q => decide (y.head j ≠ u.slot i j)) (List.finRange Q)
  · intro j hj
    obtain ⟨k, _, hk⟩ := List.mem_map.mp hj
    exact hk ▸ Nat.le_of_lt k.isLt

private theorem before_small (a : Data) (S : ℕ)
    (hm : ∀ j ∈ UniversalRowAssembly.boundInputPorts, (a.stacks j).length ≤ S)
    (hr : r ≤ S) (hQ : Q ≤ S) (hxs : xs.length ≤ S) (hw : MatrixWordEncoding.width p ≤ S) :
    small (8 * (S + 1) ^ 2) (UniversalRowAssembly.beforeData p i u y xs a).stacks := by
  have hs : S ≤ 8 * (S + 1) ^ 2 := by
    have := (square_arithmetic S).2.1
    omega
  have hstaged : small (8 * (S + 1) ^ 2)
      (UniversalRowAssembly.stagedStacks (r := r) (Q := Q) p xs a) := by
    intro j hj
    rcases hj with ⟨k, rfl⟩ | hj
    · have hh := input_length_le a Q r xs.length (MatrixWordEncoding.width p) S
        hm hQ hr hxs hw k
      simp only [UniversalRowAssembly.stagedStacks, port_injective.extend_apply]
      omega
    · simpa only [UniversalRowAssembly.stagedStacks,
        Function.extend_apply' _ _ _ (master_disjoint j hj)] using (hm j hj).trans hs
  have hvec : (CorrectionVectorProgram.vector p i u y xs 0 Q).length ≤ 8 * (S + 1) ^ 2 := by
    rw [CorrectionVectorProgram.vector_length]
    have hh := (Nat.mul_le_mul hQ hw).trans (square_arithmetic S).2.2.1
    nlinarith only [hh]
  have hindex : (UniversalRowTermProgram.indices (UniversalRowAssembly.selected i u y)).length ≤
      8 * (S + 1) ^ 2 := by
    have hh := selected_indices_length_le i u y
    have hmul := Nat.mul_le_mul (show 2 * Q + 2 ≤ 2 * S + 2 by omega) hQ
    have hsquare := (square_arithmetic S).2.2.2
    omega
  have hdelta : (UniversalRowAssembly.deltaWord u y a).length ≤ 8 * (S + 1) ^ 2 := by
    unfold UniversalRowAssembly.deltaWord
    split_ifs
    · exact (hm 132 (by decide)).trans hs
    · exact (hm 131 (by decide)).trans hs
  unfold UniversalRowAssembly.beforeData
  apply small_update
  · apply small_update _ _ _ (by simp)
    apply small_update _ _ _ (by simp)
    apply small_update
    · exact small_update (small_update hstaged _ _ hvec) _ _ hindex
    · exact (hm 132 (by decide)).trans hs
  · exact hdelta

/-- Every relevant word after the fixed rearrangement has a concrete bound. -/
theorem afterData_length_le (a : Data) (S : ℕ)
    (hm : ∀ j ∈ UniversalRowAssembly.boundInputPorts, (a.stacks j).length ≤ S)
    (hr : r ≤ S) (hQ : Q ≤ S) (hxs : xs.length ≤ S) (hw : MatrixWordEncoding.width p ≤ S)
    (j : Fin 49) :
    ((UniversalRowAssembly.afterData p i u y xs a).stacks (port j)).length ≤
      2 ^ 26 * (S + 1) ^ 2 := by
  have h := result_small UniversalRowRearrange.operations
    (UniversalRowAssembly.beforeData p i u y xs a) (8 * (S + 1) ^ 2)
    (before_small p i u y xs a S hm hr hQ hxs hw) operation_inputs
  have hj := h (port j) (active_port j)
  change _ ≤ 2 ^ 23 * (8 * (S + 1) ^ 2) at hj
  rw [UniversalRowAssembly.afterData]
  calc
    _ ≤ 2 ^ 23 * (8 * (S + 1) ^ 2) := hj
    _ = 2 ^ 26 * (S + 1) ^ 2 := by ring

/-- The actual rearrangement cost is bounded using only the original masters. -/
theorem rearrange_cost_le (a : Data) (S : ℕ)
    (hm : ∀ j ∈ UniversalRowAssembly.boundInputPorts, (a.stacks j).length ≤ S)
    (hr : r ≤ S) (hQ : Q ≤ S) (hxs : xs.length ≤ S) (hw : MatrixWordEncoding.width p ≤ S) :
    UniversalRowRearrange.cost UniversalRowRearrange.operations
      (UniversalRowAssembly.beforeData p i u y xs a) ≤ rearrangeBound S := by
  have h := cost_potential UniversalRowRearrange.operations
    (UniversalRowAssembly.beforeData p i u y xs a) (8 * (S + 1) ^ 2)
    (before_small p i u y xs a S hm hr hQ hxs hw) operation_inputs
  change _ + 7 * (8 * (S + 1) ^ 2) ≤
    7 * (2 ^ 23 * (8 * (S + 1) ^ 2)) + 5 * 23 at h
  have hs := (square_arithmetic S).1
  unfold rearrangeBound
  norm_num at h ⊢
  omega

/-- Moving source code out of the workspace erases its length from cleanup. -/
theorem afterMove_length_le (t : UniversalRowLoop.Tables) (a : Data) (S : ℕ)
    (hm : ∀ j ∈ UniversalRowAssembly.boundInputPorts, (a.stacks j).length ≤ S)
    (hr : r ≤ S) (hQ : Q ≤ S) (hxs : xs.length ≤ S) (hw : MatrixWordEncoding.width p ≤ S)
    (j : Fin 49) :
    ((UniversalRowAssembly.afterMove p i u y xs t a).stacks (port j)).length ≤
      2 ^ 26 * (S + 1) ^ 2 := by
  have h := afterData_length_le p i u y xs a S hm hr hQ hxs hw j
  have hcode := UniversalRowWorkspace.port_ne_code j
  change ((Function.update (Function.update (Function.update
    (Function.update (Function.update (UniversalRowAssembly.afterData p i u y xs a).stacks
      (port 18) []) (port 31) (UniversalRowAssembly.sourceWord p i u y xs t a))
      (port 31) []) (port 44) []) 26 (UniversalRowAssembly.sourceWord p i u y xs t a))
      (port j)).length ≤ _
  simp only [Function.update_of_ne hcode, Function.update_idem, Function.update_apply]
  split_ifs <;> first | exact Nat.zero_le _ | exact h

/-- The actual 49-stack cleanup bound holds for every generated table/source. -/
theorem cleanup_cost_le (t : UniversalRowLoop.Tables) (a : Data) (S : ℕ)
    (hm : ∀ j ∈ UniversalRowAssembly.boundInputPorts, (a.stacks j).length ≤ S)
    (hr : r ≤ S) (hQ : Q ≤ S) (hxs : xs.length ≤ S) (hw : MatrixWordEncoding.width p ≤ S) :
    UniversalRowWorkspace.clearCost UniversalRowWorkspace.workPorts
      (UniversalRowAssembly.afterMove p i u y xs t a) ≤ cleanupBound S := by
  have h := UniversalRowWorkspace.clearCost_bound UniversalRowWorkspace.workPorts
    (UniversalRowAssembly.afterMove p i u y xs t a) (2 ^ 26 * (S + 1) ^ 2) (by
      intro j hj
      obtain ⟨k, rfl⟩ := (UniversalRowWorkspace.mem_workPorts j).mp hj
      exact afterMove_length_le p i u y xs t a S hm hr hQ hxs hw k)
  rw [UniversalRowWorkspace.workPorts_length] at h
  have hs := (square_arithmetic S).1
  unfold cleanupBound
  norm_num at h ⊢
  omega

end SubexponentialSAT.Subexp.UniversalRowWorkspaceBound

end OAI.Algorithms
