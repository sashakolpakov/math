import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFWidthDriver
import OAI.Algorithms.SubexponentialSAT.ExecSunflowerSearchBridge
import OAI.Algorithms.SubexponentialSAT.ExecSunflowerCodeTransport

namespace OAI.Algorithms

/-!
# Minimum-width correctness of the actual encoded driver

The proof follows the driver's concrete execution log. A failed stage has
exhausted its real index-and-mask loop. A successful stage is the last stage
executed, so no later width can replace its materialized witness.
-/

namespace SubexponentialSAT.ExecCNFWidthCorrectness

open BitProgram StructuredCalls
open ExecCNFWidthDriver

def Normalized (F : Formula) (k : ℕ) : Prop :=
  (F.map ExecCNF.clauseSet).Nodup ∧
  (∀ C ∈ F, C.Nodup) ∧ (∀ C ∈ F, C.length ≤ k)

def NumericFrame {k : ℕ} (F : Formula) (limit : List Bool) (z : ℕ → ℕ)
    (a : Data k) : Prop :=
  BinaryArithmetic.toNat limit = F.length ∧
  CounterPrograms.value (a.stacks (low k 20)) = DyadicWidth.width F.length ∧
  ∀ d : Width k,
    BinaryArithmetic.toNat
      (a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))) = z (dimension d)

def Free (F : Formula) (z : ℕ → ℕ) (d : ℕ) : Prop :=
  Sunflower.NonemptyCoreSunflowerFree
    ((ExecCNF.formulaSet F).filter (fun C => C.card = d)) (z d)

def Accepted {k : ℕ} (F : Formula) (limit : List Bool) (z : ℕ → ℕ)
    (d : Width k) (a : Data k) : Prop :=
  a.stacks (low k 14) = (dimension d).bits ∧
  BinaryArithmetic.toNat (a.stacks (low k 15)) = z (dimension d) ∧
  ExecSunflowerCallback.Saved F limit (dimension d).bits
    (a.stacks (low k 15)) (localState a)

def Result {k : ℕ} (F : Formula) (limit : List Bool) (z : ℕ → ℕ)
    (ds : List (Width k)) (a : Data k) : Prop :=
  (a.stacks (low k 21) = [] ∧ ∀ d ∈ ds, Free F z (dimension d)) ∨
  (a.stacks (low k 21) ≠ [] ∧ ∃ d ∈ ds, Accepted F limit z d a ∧
    ∀ j ∈ ds, dimension j < dimension d → Free F z (dimension j))

theorem ready_empty {k : ℕ} (F : Formula) (limit : List Bool) (a : Data k)
    (ha : Ready F limit a) : a.stacks (low k 21) = [] :=
  ha.2.2 21 (by decide)

theorem numeric_frame {k : ℕ} (F : Formula) (limit : List Bool) (z : ℕ → ℕ)
    (a b : Data k) (h : NumericFrame F limit z a) (hf : StageFrame k a b) :
    NumericFrame F limit z b := by
  refine ⟨h.1, ?_, ?_⟩
  · rw [hf (low k 20) ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))]
    exact h.2.1
  · intro d
    rw [hf _ (ExecCNFWidthLoad.bank_ne_low k (dimension d) (dimension_le d) 8)
      (ExecCNFWidthLoad.bank_ne_low k (dimension d) (dimension_le d) 13)
      (ExecCNFWidthLoad.bank_ne_low k (dimension d) (dimension_le d) 14)
      (ExecCNFWidthLoad.bank_ne_low k (dimension d) (dimension_le d) 15)
      (ExecCNFWidthLoad.bank_ne_low k (dimension d) (dimension_le d) 17)
      (ExecCNFWidthLoad.bank_ne_low k (dimension d) (dimension_le d) 21)]
    exact h.2.2 d

theorem accepted_of_stacks_eq {k : ℕ} (F : Formula) (limit : List Bool) (z : ℕ → ℕ)
    (d : Width k) (a b : Data k) (ha : Accepted F limit z d a)
    (hs : b.stacks = a.stacks) : Accepted F limit z d b := by
  refine ⟨by simpa only [hs] using ha.1, by simpa only [hs] using ha.2.1, ?_⟩
  intro hn
  change b.stacks (low k 21) ≠ [] at hn
  have hn' : (localState a).stacks 21 ≠ [] := by
    change a.stacks (low k 21) ≠ []
    simpa only [hs] using hn
  obtain ⟨mask, words, ht, hv, hG, hH⟩ := ha.2.2 hn'
  change a.stacks (low k 21) = CandidatePrepareProgram.tupleCode (mask :: words) at ht
  change a.stacks (low k 13) =
    CandidatePrepareProgram.formulaCode (CandidatePrepareProgram.selected F words) at hG
  change a.stacks (low k 8) =
    CandidatePrepareProgram.clauseCode (CandidatePrepareProgram.core F mask words) at hH
  refine ⟨mask, words, ?_, ?_, ?_, ?_⟩
  · change b.stacks (low k 21) = _
    simpa only [hs] using ht
  · simpa only [hs] using hv
  · change b.stacks (low k 13) = _
    simpa only [hs] using hG
  · change b.stacks (low k 8) = _
    simpa only [hs] using hH

/-- Every actual failed stage supplies the mathematical exclusion at its
width; successful stages supply the retained checker witness. -/
theorem stage_semantics {k : ℕ} (d : Width k) (F : Formula) (limit : List Bool)
    (z : ℕ → ℕ) (hz : ∀ d : Width k, 0 < z (dimension d))
    (hF : Normalized F k) (a b : Data k) (ha : Ready F limit a)
    (hn : NumericFrame F limit z a) {t : ℕ} (he : Eval (stage k d) t a b) :
    StageFrame k a b ∧ NumericFrame F limit z b ∧ Accepted F limit z d b ∧
      (b.stacks (low k 21) = [] → Ready F limit b ∧ Free F z (dimension d)) := by
  obtain ⟨t', e, hrun, _, hd, hr, _, _, hsave, hf, hready, hnone⟩ :=
    stage_eval k d F limit a ha
  have hab := he.final_unique (low k 16) hrun
  subst e
  have hrows : BinaryArithmetic.toNat (b.stacks (low k 15)) = z (dimension d) :=
    (congrArg BinaryArithmetic.toNat hr).trans (hn.2.2 d)
  refine ⟨hf, numeric_frame F limit z a b hn hf, ⟨hd, hrows, ?_⟩, ?_⟩
  · simpa only [hr] using hsave
  · intro hempty
    refine ⟨hready hempty, ?_⟩
    have hno : ∀ mask words, mask.length = k →
        words.map List.length = List.replicate
          (BinaryArithmetic.toNat (a.stacks
            (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))))
          (DyadicWidth.width F.length) →
        ExecSunflowerSearchSpec.accept F mask limit (dimension d).bits
          (a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))) words ≠ true := by
      intro mask words hm hw
      have hfalse := hnone hempty mask words hm (by
        rw [hn.2.1, CounterPrograms.value_eq_toNat]
        exact hw)
      intro htrue
      change ExecSunflowerCallback.accepted F mask limit (dimension d).bits
        (a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d))) words = true at htrue
      rw [hfalse] at htrue
      contradiction
    have hfree := ExecSunflowerSearchSpec.free_of_no_accept F k limit (dimension d).bits
      (a.stacks (ExecCNFWidthLoad.bank k (dimension d) (dimension_le d)))
      hF.1 hF.2.1 hF.2.2 hn.1 (by rw [hn.2.2 d]; exact hz d) hno
    simpa only [Free, ArithmeticExpressionSupport.bits_value, hn.2.2 d] using hfree

theorem visits_result {k : ℕ} {ds visited : List (Width k)} {t : ℕ} {a b : Data k}
    (h : Visits k ds visited t a b) (F : Formula) (limit : List Bool) (z : ℕ → ℕ)
    (hz : ∀ d : Width k, 0 < z (dimension d)) (hF : Normalized F k) :
    Ready F limit a → NumericFrame F limit z a →
    ds.Pairwise (fun d e => dimension d < dimension e) → Result F limit z ds b := by
  induction h with
  | done a =>
      intro ha _ _
      exact Or.inl ⟨ready_empty F limit a ha, by simp⟩
  | @stopped d ds a hn =>
      intro ha _ _
      exact (hn (ready_empty F limit a ha)).elim
  | @step d ds visited a b c ns nt hzero hstage htail ih =>
      intro ha hn hpair
      have hpReady : Ready F limit (peeked a) :=
        ExecCNFWidthInvariant.ready_of_stacks_eq F limit a (peeked a) ha rfl
      have hpNum : NumericFrame F limit z (peeked a) := hn
      obtain ⟨hf, hnum, haccept, hfailed⟩ :=
        stage_semantics d F limit z hz hF (peeked a) b hpReady hpNum hstage
      obtain ⟨hfirst, hrest⟩ := List.pairwise_cons.mp hpair
      by_cases hb : b.stacks (low k 21) = []
      · obtain ⟨hbReady, hbFree⟩ := hfailed hb
        rcases ih hbReady hnum hrest with hdone | hfound
        · refine Or.inl ⟨hdone.1, ?_⟩
          intro j hj
          rcases List.mem_cons.mp hj with rfl | hj
          · exact hbFree
          · exact hdone.2 j hj
        · obtain ⟨hc, win, hwin, hw, hbefore⟩ := hfound
          refine Or.inr ⟨hc, win, List.mem_cons_of_mem _ hwin, hw, ?_⟩
          intro j hj hlt
          rcases List.mem_cons.mp hj with rfl | hj
          · exact hbFree
          · exact hbefore j hj hlt
      · have hs : c.stacks = b.stacks := htail.stopped_stacks hb
        refine Or.inr ⟨by simpa only [hs] using hb, d, List.mem_cons_self,
          accepted_of_stacks_eq F limit z d b c haccept hs, ?_⟩
        intro j hj hlt
        rcases List.mem_cons.mp hj with rfl | hj
        · exact (Nat.lt_irrefl _ hlt).elim
        · exact (Nat.lt_asymm (hfirst j hj) hlt).elim

theorem full_range_sorted (k : ℕ) :
    (List.finRange (k - 1)).Pairwise (fun d e => dimension d < dimension e) := by
  apply (List.pairwise_lt_finRange (k - 1)).imp
  intro a b hab
  change a.val < b.val at hab
  change a.val + 2 < b.val + 2
  omega

/-- A successful complete driver run satisfies the exact minimum-width
predicate used by the existing path charging proof. -/
theorem driver_result {k : ℕ} {visited : List (Width k)} {t : ℕ} {a b : Data k}
    (h : Visits k (List.finRange (k - 1)) visited t a b)
    (F : Formula) (limit : List Bool) (z : ℕ → ℕ)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 0 < z j) (hF : Normalized F k)
    (ha : Ready F limit a) (hn : NumericFrame F limit z a) :
    (b.stacks (low k 21) = [] ∧ ∀ j, 2 ≤ j → j ≤ k → Free F z j) ∨
    (b.stacks (low k 21) ≠ [] ∧ ∃ d : Width k, Accepted F limit z d b ∧
      InsertionInvariant.MinimumWidth z (ExecCNF.formulaSet F) (dimension d)) := by
  have hh := visits_result h F limit z
    (fun d => hz (dimension d) (by dsimp [dimension]; omega) (dimension_le d))
    hF ha hn (full_range_sorted k)
  rcases hh with hnone | hsome
  · refine Or.inl ⟨hnone.1, ?_⟩
    intro j hj hk
    let d : Width k := ⟨j - 2, by omega⟩
    have hd : dimension d = j := by dsimp [dimension, d]; omega
    simpa only [hd] using hnone.2 d (List.mem_finRange d)
  · obtain ⟨hfilled, d, _, haccept, hbefore⟩ := hsome
    refine Or.inr ⟨hfilled, d, haccept, ?_⟩
    intro j hj hjd
    have hdk := dimension_le d
    let e : Width k := ⟨j - 2, by omega⟩
    have he : dimension e = j := by dsimp [dimension, e]; omega
    simpa only [he, Free] using hbefore e (List.mem_finRange e) (by omega)

end SubexponentialSAT.ExecCNFWidthCorrectness

end OAI.Algorithms
