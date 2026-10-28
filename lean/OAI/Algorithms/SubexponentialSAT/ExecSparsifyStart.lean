import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyProgram

namespace OAI.Algorithms

/-! The node search's clean entry conditions follow from bounded extraction. -/

namespace SubexponentialSAT.ExecSparsifyProgram

open BitProgram StructuredCalls ExecSparsifyNode

def CleanEntry {k : ℕ} (a : Data k) : Prop :=
  ∀ i : Fin (k + 39), 2 ≤ i.val → i.val < 37 → a.stacks i = []

theorem head_fresh {k : ℕ} (F : CandidatePrepareProgram.Formula) (a : Data k)
    (ha : CleanEntry a) :
    ExecCNFNodeSearch.Fresh F
      (projectState id (searchPort k) (headLoaded (CandidatePrepareProgram.formulaCode F) a)) := by
  constructor
  · change (Function.update a.stacks (port k 21)
      (CandidatePrepareProgram.formulaCode F)) (port k 21) =
        CandidatePrepareProgram.formulaCode F
    exact Function.update_self _ _ _
  · intro i hi
    have hi16 : i ≠ 16 := by
      intro he
      subst i
      exact (show ¬ ExecCNFWidthInvariant.Scratch (16 : Fin 32) by decide) hi
    have hport : searchPort k (ExecCNFWidthLoad.low k i) ≠ port k 21 := by
      intro he
      apply hi16
      apply Fin.ext
      have hv := congrArg Fin.val he
      change 5 + i.val = 21 at hv
      omega
    change (headLoaded (CandidatePrepareProgram.formulaCode F) a).stacks
      (searchPort k (ExecCNFWidthLoad.low k i)) = []
    rw [headLoaded_stack_frame a (CandidatePrepareProgram.formulaCode F) _ hport]
    apply ha
    · change 2 ≤ 5 + i.val
      omega
    · change 5 + i.val < 37
      omega
  · change (headLoaded (CandidatePrepareProgram.formulaCode F) a).stacks
      (port k 24) = []
    rw [headLoaded_stack_frame a (CandidatePrepareProgram.formulaCode F) (port k 24)
      ((port_injective k).ne (by decide : (24 : Fin 39) ≠ 21))]
    exact ha (port k 24) (by change 2 ≤ (24 : ℕ); omega) (by change (24 : ℕ) < 37; omega)
  · change (headLoaded (CandidatePrepareProgram.formulaCode F) a).stacks
      (port k 25) = []
    rw [headLoaded_stack_frame a (CandidatePrepareProgram.formulaCode F) (port k 25)
      ((port_injective k).ne (by decide : (25 : Fin 39) ≠ 21))]
    exact ha (port k 25) (by change 2 ≤ (25 : ℕ); omega) (by change (25 : ℕ) < 37; omega)

def start (k : ℕ) : Code k := .seq (readHead k) (search k)

/-- The complete start stage reads the bounded head, computes node sizes,
and executes the actual width driver. All fresh-workspace premises are
derived from the node boundary. -/
theorem start_eval {k : ℕ} (F : CandidatePrepareProgram.Formula) (a : Data k)
    (tail : List Bool) (ha : CleanEntry a)
    (h0 : a.stacks (port k 0) =
      PreserveHeadProgram.pending (CandidatePrepareProgram.formulaCode F) tail) :
    ∃ count width, CounterPrograms.value count = F.length ∧
      CounterPrograms.value width = DyadicWidth.width F.length ∧
      ∃ (ns nt : ℕ) (visited : List (ExecCNFWidthDriver.Width k)) (b : ExecCNFNodeSearch.Data k),
        ns ≤ ExecCNFNodeSearch.setupBound F ∧
        Eval (start k)
          ((24 * (CandidatePrepareProgram.formulaCode F).length + 29) + (ns + nt + 2)) a
          (embedState id (searchPort k)
            (headLoaded (CandidatePrepareProgram.formulaCode F) a) b) ∧
        ExecCNFWidthDriver.Visits k (List.finRange (k - 1)) visited nt
          (ExecCNFNodeSearch.prepared
            (projectState id (searchPort k) (headLoaded (CandidatePrepareProgram.formulaCode F) a))
            count width) b := by
  let h := headLoaded (CandidatePrepareProgram.formulaCode F) a
  let p := projectState id (searchPort k) h
  have hhead := readHead_eval a (CandidatePrepareProgram.formulaCode F) tail h0
    (ha (port k 21) (by change 2 ≤ (21 : ℕ); omega) (by change (21 : ℕ) < 37; omega))
    (ha (port k 5) (by change 2 ≤ (5 : ℕ); omega) (by change (5 : ℕ) < 37; omega))
    (ha (port k 6) (by change 2 ≤ (6 : ℕ); omega) (by change (6 : ℕ) < 37; omega))
  obtain ⟨count, width, hc, hw, _, _, ns, nt, visited, b, hns, htrace, hvisit,
    _, _, _, _, _, _⟩ := ExecCNFNodeSearch.program_runs k F p (head_fresh F a ha)
  have hsearch := eval_call_from_state (ExecCNFNodeSearch.program k) id (searchPort k)
    h Function.injective_id (searchPort_injective k) htrace
  exact ⟨count, width, hc, hw, ns, nt, visited, b, hns, hhead.seq hsearch, hvisit⟩

end SubexponentialSAT.ExecSparsifyProgram

end OAI.Algorithms
