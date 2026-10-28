import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFWidthLoad
import OAI.Algorithms.SubexponentialSAT.ExecCNFTupleInitialize
import OAI.Algorithms.SubexponentialSAT.CandidatePrepareProgram

namespace OAI.Algorithms

/-!
# The clean boundary between two candidate-search widths

The tuple initializer needs scratch 27 and 28 in addition to the callback's
work stacks. This common boundary includes those stacks, the empty tuple and
odometer scratch, and empty witness/core/family outputs. It places no condition
on Boolean registers. Loading the next width and threshold preserves it.
-/

namespace SubexponentialSAT.ExecCNFWidthInvariant

open BitProgram StructuredCalls
open ExecCNFWidthLoad (low bank)

abbrev Formula := CandidatePrepareProgram.Formula
abbrev Data := ExecCNFWidthLoad.Data

def Scratch (i : Fin 32) : Prop :=
  i.val < 14 ∨ i = 17 ∨ i = 18 ∨ (21 ≤ i.val ∧ i.val ≤ 28)

instance (i : Fin 32) : Decidable (Scratch i) := inferInstanceAs (Decidable
  (i.val < 14 ∨ i = 17 ∨ i = 18 ∨ (21 ≤ i.val ∧ i.val ≤ 28)))

def Clean {k : ℕ} (a : Data k) : Prop :=
  ∀ i : Fin 32, Scratch i → a.stacks (low k i) = []

def Ready {k : ℕ} (F : Formula) (limit : List Bool) (a : Data k) : Prop :=
  a.stacks (low k 16) = CandidatePrepareProgram.formulaCode F ∧
  a.stacks (low k 19) = limit ∧ Clean a

def localState {k : ℕ} (a : Data k) : State 32 32 := projectState id (low k) a

theorem scratch_ne_width (i : Fin 32) (hi : Scratch i) : i ≠ 14 := by
  intro h
  subst i
  exact (show ¬ Scratch (14 : Fin 32) by decide) hi

theorem scratch_ne_threshold (i : Fin 32) (hi : Scratch i) : i ≠ 15 := by
  intro h
  subst i
  exact (show ¬ Scratch (15 : Fin 32) by decide) hi

/-- Replacing every register leaves the boundary unchanged. -/
theorem clean_of_stacks_eq {k : ℕ} (a b : Data k) (ha : Clean a)
    (h : b.stacks = a.stacks) : Clean b := by
  intro i hi
  simpa only [h] using ha i hi

theorem ready_of_stacks_eq {k : ℕ} (F : Formula) (limit : List Bool)
    (a b : Data k) (ha : Ready F limit a) (h : b.stacks = a.stacks) :
    Ready F limit b := by
  exact ⟨by simpa only [h] using ha.1,
    by simpa only [h] using ha.2.1, clean_of_stacks_eq a b ha.2.2 h⟩

theorem clean_of_width_frame {k : ℕ} (a b : Data k) (ha : Clean a)
    (h : ∀ i, i ≠ low k 14 → i ≠ low k 15 → b.stacks i = a.stacks i) :
    Clean b := by
  intro i hi
  exact (h (low k i)
    ((ExecCNFWidthLoad.low_injective k).ne (scratch_ne_width i hi))
    ((ExecCNFWidthLoad.low_injective k).ne (scratch_ne_threshold i hi))).trans (ha i hi)

theorem clean_preparation {k : ℕ} (a : Data k) (ha : Clean a) :
    CandidatePrepareProgram.WorkEmpty (localState a) := by
  refine ⟨?_, ha 8 (by decide), ha 13 (by decide), ha 22 (by decide),
    ha 23 (by decide), ha 24 (by decide), ha 25 (by decide), ha 26 (by decide)⟩
  intro i
  apply ha (Fin.castAdd 25 i)
  left
  exact Nat.lt_trans i.isLt (by decide)

theorem clean_workspace {k : ℕ} (a : Data k) (ha : Clean a) :
    ∀ i : Fin 13, i ≠ 8 → (localState a).stacks (Fin.castAdd 19 i) = [] := by
  intro i _
  apply ha (Fin.castAdd 19 i)
  left
  exact Nat.lt_trans i.isLt (by decide)

theorem clean_tupleInitializer {k : ℕ} (a : Data k) (ha : Clean a) :
    ExecCNFTupleInitialize.Ready (localState a) :=
  ⟨⟨ha 17 (by decide), ha 24 (by decide), ha 25 (by decide), ha 26 (by decide),
    ha 27 (by decide), ha 28 (by decide)⟩, ha 22 (by decide), ha 23 (by decide)⟩

theorem clean_counter {k : ℕ} (a : Data k) (ha : Clean a) :
    (localState a).stacks 17 = [] ∧ (localState a).stacks 18 = [] ∧
      (localState a).stacks 21 = [] :=
  ⟨ha 17 (by decide), ha 18 (by decide), ha 21 (by decide)⟩

/-- The callback's complete fresh-search input invariant, stated using the
existing preparation workspace and the exact additional checker workspace.
The implication permits the callback's usual skip-after-success convention. -/
theorem callback_inputs {k : ℕ} (F : Formula) (limit : List Bool)
    (a : Data k) (ha : Ready F limit a) :
    (localState a).stacks 21 = [] →
      (localState a).stacks 16 = CandidatePrepareProgram.formulaCode F ∧
      (localState a).stacks 19 = limit ∧
      CandidatePrepareProgram.WorkEmpty (localState a) ∧
      (∀ i : Fin 13, i ≠ 8 → (localState a).stacks (Fin.castAdd 19 i) = []) ∧
      (localState a).stacks 14 = a.stacks (low k 14) ∧
      (localState a).stacks 15 = a.stacks (low k 15) := by
  intro _
  exact ⟨ha.1, ha.2.1, clean_preparation a ha.2.2, clean_workspace a ha.2.2, rfl, rfl⟩

/-- The failed-search endpoint restores the same common boundary. The frame
is exactly the one returned by the concrete one-width search: only core 8,
family 13, tuple 17 and witness 21 may differ. The success path instead stops
the outer driver before another load. -/
theorem ready_after_unsuccessful_search {k : ℕ} (F : Formula) (limit : List Bool)
    (a b : Data k) (ha : Ready F limit a)
    (h8 : b.stacks (low k 8) = []) (h13 : b.stacks (low k 13) = [])
    (h17 : b.stacks (low k 17) = []) (h21 : b.stacks (low k 21) = [])
    (hf : ∀ i : Fin 32, i ≠ 8 → i ≠ 13 → i ≠ 17 → i ≠ 21 →
      b.stacks (low k i) = a.stacks (low k i)) : Ready F limit b := by
  refine ⟨(hf 16 (by decide) (by decide) (by decide) (by decide)).trans ha.1,
    (hf 19 (by decide) (by decide) (by decide) (by decide)).trans ha.2.1, ?_⟩
  intro i hi
  by_cases hi8 : i = 8
  · subst i; exact h8
  by_cases hi13 : i = 13
  · subst i; exact h13
  by_cases hi17 : i = 17
  · subst i; exact h17
  by_cases hi21 : i = 21
  · subst i; exact h21
  exact (hf i hi8 hi13 hi17 hi21).trans (ha.2.2 i hi)

/-- Relocating the fixed 32-stack search preserves arbitrary stack contents
at every other ambient port, including local 30/31 and the entire high bank.
Only the actual search outputs and its tuple port may have changed. -/
theorem embed_search_frame {k : ℕ} (a : Data k) (b : State 32 32)
    (hf : ∀ i : Fin 32, i ≠ 8 → i ≠ 13 → i ≠ 17 → i ≠ 21 →
      b.stacks i = (localState a).stacks i) :
    ∀ i : Fin (k + 34), i ≠ low k 8 → i ≠ low k 13 →
      i ≠ low k 17 → i ≠ low k 21 →
      (embedState id (low k) a b).stacks i = a.stacks i := by
  intro i hi8 hi13 hi17 hi21
  classical
  by_cases hi : ∃ j, low k j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [embedState_stack id (low k) a b (ExecCNFWidthLoad.low_injective k) j]
    exact hf j (fun h => hi8 (congrArg (low k) h))
      (fun h => hi13 (congrArg (low k) h))
      (fun h => hi17 (congrArg (low k) h))
      (fun h => hi21 (congrArg (low k) h))
  · exact embedState_stack_frame id (low k) a b i hi

/-- An actual width/threshold load preserves every work stack, including the
initializer's additional 27/28 scratch pair. No register reset is assumed. -/
theorem load_ready (k d : ℕ) (hd : d ≤ k) (F : Formula) (limit : List Bool)
    (a : Data k) (ha : Ready F limit a) :
    ∃ b : Data k,
      Eval (ExecCNFWidthLoad.command k d hd) (ExecCNFWidthLoad.bound k d hd a) a b ∧
      Ready F limit b ∧ b.stacks (low k 14) = d.bits ∧
      b.stacks (low k 15) = a.stacks (bank k d hd) ∧
      ExecCNFTupleInitialize.Ready (localState b) ∧
      (localState b).stacks 18 = [] ∧ (localState b).stacks 21 = [] ∧
      (∀ i, i ≠ low k 14 → i ≠ low k 15 → b.stacks i = a.stacks i) := by
  obtain ⟨b, he, h14, h15, hf⟩ := ExecCNFWidthLoad.command_eval k d hd a
    (ha.2.2 25 (by decide))
  have hb : Ready F limit b := by
    refine ⟨?_, ?_, clean_of_width_frame a b ha.2.2 hf⟩
    · exact (hf (low k 16) ((ExecCNFWidthLoad.low_injective k).ne (by decide))
        ((ExecCNFWidthLoad.low_injective k).ne (by decide))).trans ha.1
    · exact (hf (low k 19) ((ExecCNFWidthLoad.low_injective k).ne (by decide))
        ((ExecCNFWidthLoad.low_injective k).ne (by decide))).trans ha.2.1
  exact ⟨b, he, hb, h14, h15, clean_tupleInitializer b hb.2.2,
    hb.2.2 18 (by decide), hb.2.2 21 (by decide), hf⟩

end SubexponentialSAT.ExecCNFWidthInvariant

end OAI.Algorithms
