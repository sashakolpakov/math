import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFNodeSearchCorrectness
import OAI.Algorithms.SubexponentialSAT.ExecCNFWidthDriverCosts
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace

namespace OAI.Algorithms

/-!
# Actual node-setup and search costs in the same execution

Both size words are computed by the setup program. The following bounds use
the concrete costed width-driver execution and retain its exact visit log.
No uniform cost for an arbitrary callback or unbounded state is assumed.
-/

namespace SubexponentialSAT.ExecCNFNodeSearchCosts

open BitProgram StructuredCalls
open ExecCNFNodeSearch
open ExecCNFWidthLoad (low)

noncomputable def bound (k : ℕ) (F : Formula) (a : Data k) (count width : List Bool) : ℕ :=
  setupBound F + ExecCNFWidthDriver.totalBound k F count (prepared a count width) + 1

theorem command_eval (k : ℕ) (F : Formula) (a : Data k) (ha : Fresh F a) :
    ∃ count width, CounterPrograms.value count = F.length ∧
      CounterPrograms.value width = DyadicWidth.width F.length ∧
      count.length ≤ F.length ∧ width.length ≤ F.length + 1 ∧
      ∃ (ns nt : ℕ) (visited : List (ExecCNFWidthDriver.Width k)) (b : Data k),
        ns ≤ setupBound F ∧
        nt + 1 ≤ ExecCNFWidthDriver.totalBound k F count (prepared a count width) ∧
        Eval (ExecCNFNodeSearch.command k) (ns + nt + 1) a b ∧
        ExecCNFWidthDriver.Visits k (List.finRange (k - 1)) visited nt
          (prepared a count width) b ∧
        visited <+: List.finRange (k - 1) ∧
        (b.stacks (low k 21) = [] → ExecCNFWidthInvariant.Ready F count b) ∧
        b.stacks (low k 16) = CandidatePrepareProgram.formulaCode F ∧
        b.stacks (low k 19) = count ∧ b.stacks (low k 20) = width ∧ Frame k a b := by
  obtain ⟨count, width, hc, hw, hcl, hwl, ns, hns, hsetup, hready⟩ :=
    ExecCNFNodeSearch.setup_eval k F a ha
  obtain ⟨visited, nt, b, htrace, hnt, hvisit, hprefix, hb, hf⟩ :=
    ExecCNFWidthDriver.program_runs_costed k F count (prepared a count width) hready
  refine ⟨count, width, hc, hw, hcl, hwl, ns, nt, visited, b, hns, hnt, ?_,
    hvisit, hprefix, hb, ?_, ?_, ?_, ?_⟩
  · have he := hsetup.seq (Eval.call _ htrace)
    simpa only [ExecCNFNodeSearch.command, Nat.add_assoc] using he
  · exact (hf (low k 16)
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))).trans hready.1
  · exact (hf (low k 19)
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))).trans
        (prepared_count a count width)
  · exact (hf (low k 20)
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))
      ((ExecCNFWidthLoad.low_injective k).ne (by decide))).trans
        (prepared_width a count width)
  · intro i hi8 hi13 hi14 hi15 hi17 hi19 hi20 hi21
    exact (hf i hi8 hi13 hi14 hi15 hi17 hi21).trans
      (prepared_frame a count width i hi19 hi20)

/-- The same actual run supplies its total instruction bound, visit log,
computed words, and bound on its final local storage. -/
theorem program_runs (k : ℕ) (F : Formula) (a : Data k) (ha : Fresh F a) :
    ∃ count width, CounterPrograms.value count = F.length ∧
      CounterPrograms.value width = DyadicWidth.width F.length ∧
      count.length ≤ F.length ∧ width.length ≤ F.length + 1 ∧
      ∃ (ns nt : ℕ) (visited : List (ExecCNFWidthDriver.Width k)) (b : Data k),
        ns ≤ setupBound F ∧
        nt + 1 ≤ ExecCNFWidthDriver.totalBound k F count (prepared a count width) ∧
        Trace (ExecCNFNodeSearch.program k) (ns + nt + 2)
          (a.withPC (some (ExecCNFNodeSearch.program k).entry)) (b.withPC none) ∧
        ns + nt + 2 ≤ bound k F a count width ∧
        ExecCNFWidthDriver.Visits k (List.finRange (k - 1)) visited nt
          (prepared a count width) b ∧
        visited <+: List.finRange (k - 1) ∧
        (b.stacks (low k 21) = [] → ExecCNFWidthInvariant.Ready F count b) ∧
        b.stacks (low k 16) = CandidatePrepareProgram.formulaCode F ∧
        b.stacks (low k 19) = count ∧ b.stacks (low k 20) = width ∧ Frame k a b ∧
        stackBits b.stacks ≤ stackBits a.stacks + bound k F a count width := by
  obtain ⟨count, width, hc, hw, hcl, hwl, ns, nt, visited, b,
    hns, hnt, he, hv, hp, hr, h16, h19, h20, hf⟩ := command_eval k F a ha
  have htrace : Trace (ExecCNFNodeSearch.program k) (ns + nt + 2)
      (a.withPC (some (ExecCNFNodeSearch.program k).entry)) (b.withPC none) := by
    simpa only [ExecCNFNodeSearch.program, Nat.add_assoc] using
      compiled_halt_trace he (low k 16) (low k 21)
  have ht : ns + nt + 2 ≤ bound k F a count width := by
    unfold bound
    omega
  have hspace := BitProgram.trace_dataBits (ExecCNFNodeSearch.program k) htrace
  change stackBits b.stacks ≤ stackBits a.stacks + (ns + nt + 2) at hspace
  exact ⟨count, width, hc, hw, hcl, hwl, ns, nt, visited, b, hns, hnt,
    htrace, ht, hv, hp, hr, h16, h19, h20, hf, hspace.trans (Nat.add_le_add_left ht _)⟩

/-- The measured trace and the minimum-width outcome belong to the same
actual run. The only supplied numeric values are the persistent thresholds. -/
theorem program_correct (k : ℕ) (F : Formula) (z : ℕ → ℕ) (a : Data k)
    (ha : Fresh F a) (hF : ExecCNFWidthCorrectness.Normalized F k)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 0 < z j)
    (hb : ExecCNFNodeSearchCorrectness.BankValues z a) :
    ∃ count width, CounterPrograms.value count = F.length ∧
      CounterPrograms.value width = DyadicWidth.width F.length ∧
      count.length ≤ F.length ∧ width.length ≤ F.length + 1 ∧
      ∃ (t : ℕ) (b : Data k), t ≤ bound k F a count width ∧
        Trace (ExecCNFNodeSearch.program k) t
          (a.withPC (some (ExecCNFNodeSearch.program k).entry)) (b.withPC none) ∧
        b.stacks (low k 16) = CandidatePrepareProgram.formulaCode F ∧
        b.stacks (low k 19) = count ∧ b.stacks (low k 20) = width ∧ Frame k a b ∧
        ExecCNFNodeSearchCorrectness.Outcome F count z b ∧
        stackBits b.stacks ≤ stackBits a.stacks + bound k F a count width := by
  obtain ⟨count, width, hc, hw, hcl, hwl, ns, nt, visited, b,
    _, _, htrace, ht, hv, _, _, h16, h19, h20, hf, hspace⟩ := program_runs k F a ha
  have ho : ExecCNFNodeSearchCorrectness.Outcome F count z b :=
    ExecCNFWidthCorrectness.driver_result hv F count z hz hF
      (prepared_ready F a ha count width)
      (ExecCNFNodeSearchCorrectness.prepared_numericFrame F z a count width hc hw hb)
  exact ⟨count, width, hc, hw, hcl, hwl, ns + nt + 2, b, ht, htrace,
    h16, h19, h20, hf, ho, hspace⟩

end SubexponentialSAT.ExecCNFNodeSearchCosts

end OAI.Algorithms
