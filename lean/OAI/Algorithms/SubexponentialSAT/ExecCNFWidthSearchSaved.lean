import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFWidthSearch
import OAI.Algorithms.SubexponentialSAT.ExecSunflowerCallbackSaved

namespace OAI.Algorithms

/-! A completed one-width search either retains a matched materialized witness
or proves the absence of every candidate in its actual enumeration domain. -/

namespace SubexponentialSAT.ExecCNFWidthSearch

open BitProgram StructuredCalls ExecCNFTupleEnumeration
open ExecSunflowerCallback (Saved)

theorem saved_of_stacks_eq (F : Formula) (limit width rows : List Bool) (a b : Data)
    (ha : Saved F limit width rows a) (hs : b.stacks = a.stacks) :
    Saved F limit width rows b := by
  simpa only [Saved, hs] using ha

theorem saved_stable (F : Formula) (limit width rows : List Bool) :
    CounterForPrograms.FrameStable ports (fun _ => Saved F limit width rows) := by
  intro n a b hab ha hb21
  have ha21 : a.stacks 21 ≠ [] := by
    intro hz
    exact hb21 ((hab 21 (by decide) (by decide)).symm.trans hz)
  obtain ⟨mask, indices, ht, haccept, hG, hH⟩ := ha ha21
  exact ⟨mask, indices, (hab 21 (by decide) (by decide)).symm.trans ht, haccept,
    (hab 13 (by decide) (by decide)).symm.trans hG,
    (hab 8 (by decide) (by decide)).symm.trans hH⟩

theorem visits_saved (F : Formula) (limit width rows : List Bool) (k r w budget : ℕ)
    (hbudget : BodyBudget F limit width rows k r w budget)
    {ranks : List ℕ} {n : ℕ} {a b : Data}
    (h : Visits ports ExecSunflowerCallback.command (k :: List.replicate r w) ranks n a b)
    (hi : Invariant F limit width rows a) (hs : a.stacks 18 = [])
    (hSaved : Saved F limit width rows a) : Saved F limit width rows b := by
  induction h with
  | done => exact hSaved
  | @step tuple a e f nb na nt ranks hf hw hc he hcounter hadv htail ih =>
    have hpres := (callback_spec F limit width rows k r w budget hbudget).preserves
      tuple a e nb hw hi hc hs he
    have hnextI : Invariant F limit width rows (advanceResult ports e tuple) :=
      invariant_stable F limit width rows 0 e _ (advanceResult_outside ports e tuple) hpres.1
    have heSaved : Saved F limit width rows e := by
      cases tuple with
      | nil => simp at hw
      | cons mask indices =>
        exact ExecSunflowerCallback.saved_preserved F mask limit width rows indices a e hSaved hc
          (callback_output F mask limit width rows indices a e nb hi hc he)
    exact ih hnextI (advanceResult_scratch ports e tuple)
      (saved_stable F limit width rows 0 e _ (advanceResult_outside ports e tuple) heSaved)

/-- The retained tuple, family and core match an accepted concrete candidate.
If the witness stack is empty, every shaped candidate was rejected. -/
theorem command_eval_saved (F : Formula) (limit width : List Bool) (k budget : ℕ) (d : Data)
    (hi : Invariant F limit width (d.stacks 15) d)
    (hready : ExecCNFTupleInitialize.Ready d) (hs : d.stacks 18 = []) (h21 : d.stacks 21 = [])
    (hb : BodyBudget F limit width (d.stacks 15) k
      (CounterPrograms.value (d.stacks 15)) (CounterPrograms.value (d.stacks 20)) budget) :
    ∃ (n : ℕ) (f : Data), Eval (command k) n d f ∧
      n ≤ bound k (CounterPrograms.value (d.stacks 15))
        (CounterPrograms.value (d.stacks 20)) budget
        (ExecCNFTupleInitialize.bound k (d.stacks 15) (d.stacks 20)) ∧
      Invariant F limit width (d.stacks 15) f ∧ f.stacks 17 = [] ∧ f.stacks 18 = [] ∧
      Saved F limit width (d.stacks 15) f ∧
      (∀ i : Fin 32, i ≠ 8 → i ≠ 13 → i ≠ 17 → i ≠ 21 → f.stacks i = d.stacks i) ∧
      (f.stacks 21 = [] → ∀ (mask : List Bool) (indices : List (List Bool)), mask.length = k →
        indices.map List.length = List.replicate (CounterPrograms.value (d.stacks 15))
          (CounterPrograms.value (d.stacks 20)) →
        ExecSunflowerCallback.accepted F mask limit width (d.stacks 15) indices = false) := by
  obtain ⟨n, a, e, f, he, hn, hfi, hf17, hf18, hframe, ha21, hfs, hfe21, hai, has, nl, hlog⟩ :=
    command_eval F limit width k budget d hi hready hs hb
  have haSaved : Saved F limit width (d.stacks 15) a :=
    ExecSunflowerCallback.saved_of_empty F limit width _ a (ha21.trans h21)
  have heSaved := visits_saved F limit width _ k _ _ budget hb hlog hai has haSaved
  have hfSaved : Saved F limit width (d.stacks 15) f := by
    apply saved_stable F limit width _ 0 e f _ heSaved
    intro i hi17 _
    rw [hfs, StackRoutines.clearStacks_frame 17 i e.stacks hi17]
  refine ⟨n, f, he, hn, hfi, hf17, hf18, hfSaved, hframe, ?_⟩
  intro hf21 mask indices hm hw
  exact no_candidate_of_empty F limit width _ k _ _ budget hb hlog hai has
    (hfe21.symm.trans hf21) mask indices hm hw

end SubexponentialSAT.ExecCNFWidthSearch

end OAI.Algorithms
