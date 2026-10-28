import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCNFNodeSearch
import OAI.Algorithms.SubexponentialSAT.ExecCNFWidthCorrectness

namespace OAI.Algorithms

/-!
# The computed node parameters satisfy the minimum-width search contract

The only numeric input invariant below concerns the persistent threshold
bank. Both the formula count and the index width are derived by the actual
setup program before the concrete driver is executed.
-/

namespace SubexponentialSAT.ExecCNFNodeSearchCorrectness

open BitProgram StructuredCalls
open ExecCNFWidthLoad (low)
open ExecCNFNodeSearch

def BankValues {k : ℕ} (z : ℕ → ℕ) (a : Data k) : Prop :=
  ∀ d : ExecCNFWidthDriver.Width k,
    BinaryArithmetic.toNat (a.stacks (ExecCNFWidthLoad.bank k
      (ExecCNFWidthDriver.dimension d) (ExecCNFWidthDriver.dimension_le d))) =
        z (ExecCNFWidthDriver.dimension d)

theorem prepared_numericFrame {k : ℕ} (F : Formula) (z : ℕ → ℕ) (a : Data k)
    (count width : List Bool) (hc : CounterPrograms.value count = F.length)
    (hw : CounterPrograms.value width = DyadicWidth.width F.length)
    (hb : BankValues z a) :
    ExecCNFWidthCorrectness.NumericFrame F count z (prepared a count width) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [CounterPrograms.value_eq_toNat] using hc
  · rw [prepared_width]
    exact hw
  · intro d
    rw [prepared_frame a count width _
      (ExecCNFWidthLoad.bank_ne_low k (ExecCNFWidthDriver.dimension d)
        (ExecCNFWidthDriver.dimension_le d) 19)
      (ExecCNFWidthLoad.bank_ne_low k (ExecCNFWidthDriver.dimension d)
        (ExecCNFWidthDriver.dimension_le d) 20)]
    exact hb d

def Outcome {k : ℕ} (F : Formula) (count : List Bool) (z : ℕ → ℕ) (b : Data k) : Prop :=
  (b.stacks (low k 21) = [] ∧
    ∀ j, 2 ≤ j → j ≤ k → ExecCNFWidthCorrectness.Free F z j) ∨
  (b.stacks (low k 21) ≠ [] ∧ ∃ d : ExecCNFWidthDriver.Width k,
    ExecCNFWidthCorrectness.Accepted F count z d b ∧
      InsertionInvariant.MinimumWidth z (ExecCNF.formulaSet F)
        (ExecCNFWidthDriver.dimension d))

/-- An actual finite execution either excludes every searched width or
returns a retained accepted witness at a minimum width. There is no supplied
formula count or index-word width premise. -/
theorem command_correct (k : ℕ) (F : Formula) (z : ℕ → ℕ) (a : Data k)
    (ha : Fresh F a) (hF : ExecCNFWidthCorrectness.Normalized F k)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 0 < z j) (hb : BankValues z a) :
    ∃ count width, CounterPrograms.value count = F.length ∧
      CounterPrograms.value width = DyadicWidth.width F.length ∧
      count.length ≤ F.length ∧ width.length ≤ F.length + 1 ∧
      ∃ (ns nt : ℕ) (b : Data k), ns ≤ setupBound F ∧
        Eval (command k) (ns + nt + 1) a b ∧
        b.stacks (low k 16) = CandidatePrepareProgram.formulaCode F ∧
        b.stacks (low k 19) = count ∧ b.stacks (low k 20) = width ∧
        Frame k a b ∧ Outcome F count z b := by
  obtain ⟨count, width, hc, hw, hcl, hwl, ns, nt, visited, b,
    hns, he, hv, _, _, h16, h19, h20, hf⟩ :=
      ExecCNFNodeSearch.command_eval k F a ha
  refine ⟨count, width, hc, hw, hcl, hwl, ns, nt, b,
    hns, he, h16, h19, h20, hf, ?_⟩
  exact ExecCNFWidthCorrectness.driver_result hv F count z hz hF
    (prepared_ready F a ha count width) (prepared_numericFrame F z a count width hc hw hb)

theorem program_correct (k : ℕ) (F : Formula) (z : ℕ → ℕ) (a : Data k)
    (ha : Fresh F a) (hF : ExecCNFWidthCorrectness.Normalized F k)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 0 < z j) (hb : BankValues z a) :
    ∃ count width, CounterPrograms.value count = F.length ∧
      CounterPrograms.value width = DyadicWidth.width F.length ∧
      count.length ≤ F.length ∧ width.length ≤ F.length + 1 ∧
      ∃ (ns nt : ℕ) (b : Data k), ns ≤ setupBound F ∧
        Trace (program k) (ns + nt + 2)
          (a.withPC (some (program k).entry)) (b.withPC none) ∧
        b.stacks (low k 16) = CandidatePrepareProgram.formulaCode F ∧
        b.stacks (low k 19) = count ∧ b.stacks (low k 20) = width ∧
        Frame k a b ∧ Outcome F count z b := by
  obtain ⟨count, width, hc, hw, hcl, hwl, ns, nt, b,
    hns, he, h16, h19, h20, hf, ho⟩ := command_correct k F z a ha hF hz hb
  refine ⟨count, width, hc, hw, hcl, hwl, ns, nt, b, hns, ?_, h16, h19, h20, hf, ho⟩
  simpa only [program, one_add_one_eq_two, Nat.add_assoc] using
    compiled_halt_trace he (low k 16) (low k 21)

end SubexponentialSAT.ExecCNFNodeSearchCorrectness

end OAI.Algorithms
