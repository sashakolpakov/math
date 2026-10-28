import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SparsifyProgramMainInput

namespace OAI.Algorithms

/-! The actual Main normalizer/splitter callback at the new schedule.
The instruction bound includes normalization, singleton-worklist loading,
the full observed traversal, leaf transfer and register cleanup. -/
namespace SubexponentialSAT.SqrtLog.SparsifyProgram.Main

open Filter BitProgram StructuredCalls SubexpSetupProgram
open SubexpMainProgram (MainState workRegs persistent)
open ExecSparsifyWorklist (normalizedInput)
open ExecSparsifyObserved (encode)

abbrev procedure (c : Config) {er : ℕ} (hr : 32 ≤ workRegs er) :=
  SubexpOrderedRawSparsify.procedure c hr

def M (c : Config) (n : ℕ) := SparsificationBudgetProgram.dyadicM c.T (Asymptotic.s n)

theorem M_ge_two (c : Config) (n : ℕ) : 2 ≤ M c n :=
  SparsificationBudgetProgram.dyadicM_ge_two c.T (Asymptotic.s n)

/-- Exact identity for every instruction term in the existing Main wrapper. -/
theorem bound_eq (c : Config) {er n : ℕ} (hr : 32 ≤ workRegs er)
    (F : ExecSparsifyObserved.Formula n) (middle : MainState er (mainExtraStacks c))
    (hf : SubexpConcreteNode.FrameReady c (SubexpOrderedRawSparsify.inputFrame c hr F middle))
    (hb : SubexpConcreteNode.BankValues c (arity c.T n)
      (SubexpOrderedRawSparsify.inputFrame c hr F middle)) :
    SubexpOrderedRawSparsify.bound c hr F (M c n) (M_ge_two c n) middle hf hb =
      3500 * ((encode F).length + 1) ^ 2 + 15 * (encode (normalizedInput F)).length +
      ExecEncodedSparsifier.runCost (localFrame c hr F middle) (arity c.T n)
        (SubexpConcreteNode.local_ready c hr _ hf) (SubexpConcreteNode.local_bank c hr _ _ hb)
        (arity_ge_two c.k c.T n) (normalizedInput F) +
      6 * (Encoding.encodeList encode
        (SubexpOrderedRawSparsify.output c hr F (M c n) (M_ge_two c n) middle hf hb)).length +
      workRegs er + 39 := by
  let V := ExecWorklistLoop.nodeWork encode
    (ExecSparsifyObserved.branching (localFrame c hr F middle) (arity c.T n)
      (SubexpConcreteNode.local_ready c hr _ hf) (SubexpConcreteNode.local_bank c hr _ _ hb)
      (arity_ge_two c.k c.T n))
    (fun G => ExecSparsifyExecution.cost (localFrame c hr F middle) (arity c.T n)
      (SubexpConcreteNode.local_ready c hr _ hf) (SubexpConcreteNode.local_bank c hr _ _ hb)
      (arity_ge_two c.k c.T n) G + 1) (normalizedInput F)
  change 3500 * ((encode F).length + 1) ^ 2 +
      (15 * (encode (normalizedInput F)).length + V +
        6 * (Encoding.encodeList encode
          (SubexpOrderedRawSparsify.output c hr F (M c n) (M_ge_two c n) middle hf hb)).length +
        workRegs er + 44) + 1 =
      3500 * ((encode F).length + 1) ^ 2 + 15 * (encode (normalizedInput F)).length +
        (V + 6) + 6 * (Encoding.encodeList encode
          (SubexpOrderedRawSparsify.output c hr F (M c n) (M_ge_two c n) middle hf hb)).length +
        workRegs er + 39
  omega

/-- No old-schedule hypothesis appears: the bank and actual normalization
trace are sufficient to apply the new observed-runtime bounds. -/
theorem eventually_bound (c : Config) {er : ℕ} (hr : 32 ≤ workRegs er) :
    ∀ᶠ n : ℕ in atTop, ∀ (F : ExecSparsifyObserved.Formula n),
      ExecSunflowerSearch.RawWidthAtMost c.k F →
      ∀ (caller middle : MainState er (mainExtraStacks c)), Prepared c n caller →
      caller.stacks (persistent (mainExtraStacks c) 0) = encode F →
      SubexpOrderedRawSparsify.NormalizationRun c F caller middle →
      ∀ (hf : SubexpConcreteNode.FrameReady c (SubexpOrderedRawSparsify.inputFrame c hr F middle))
        (hb : SubexpConcreteNode.BankValues c (arity c.T n)
          (SubexpOrderedRawSparsify.inputFrame c hr F middle)),
      (SubexpOrderedRawSparsify.bound c hr F (M c n) (M_ge_two c n) middle hf hb : ℝ) ≤
        (workRegs er + 3577 : ℕ) * (((encode F).length : ℝ) + 1) ^ 2 *
          (2 : ℝ) ^ (130 * Statement.runtimeScale n) := by
  filter_upwards [eventually_runCost_target c.k c.T c.width_ge_two c.control,
    eventually_encoded_leaves_target c.k c.T c.width_ge_two c.control] with n ht hl
  intro F hF caller middle hp hbody hn hf hb
  obtain ⟨tn, _, en⟩ := hn
  obtain ⟨hready, hbank, hlength⟩ := normalized_frame c hr F hp hbody en
  have hFready := ExecSparsifyStartup.normalizedInput_ready F c.k hF
  have hanti := ExecSparsifyStartup.normalizedInput_antichain F
  have htime := ht (localFrame c hr F middle) hready hbank hlength
    (normalizedInput F) hFready hanti
  have hleaf := hl (localFrame c hr F middle) hready hbank
    (normalizedInput F) hFready hanti
  change ((Encoding.encodeList encode
    (SubexpOrderedRawSparsify.output c hr F (M c n) (M_ge_two c n) middle hf hb)).length : ℝ) ≤
      2 * (2 : ℝ) ^ (130 * Statement.runtimeScale n) at hleaf
  let E : ℝ := (2 : ℝ) ^ (130 * Statement.runtimeScale n)
  let X : ℝ := (((encode F).length : ℝ) + 1) ^ 2 * E
  have hE : 1 ≤ E := Real.one_le_rpow (by norm_num)
    (mul_nonneg (by norm_num) (Statement.runtimeScale_nonneg n))
  have hbase : 0 ≤ ((encode F).length : ℝ) := Nat.cast_nonneg _
  have hsq : 1 ≤ (((encode F).length : ℝ) + 1) ^ 2 := by nlinarith
  have hX : 1 ≤ X := one_le_mul_of_one_le_of_one_le hsq hE
  have hEX : E ≤ X := le_mul_of_one_le_left (by linarith) hsq
  have hraw : (((encode F).length : ℝ) + 1) ^ 2 ≤ X :=
    le_mul_of_one_le_right (sq_nonneg _) hE
  have hnorm : ((encode (normalizedInput F)).length : ℝ) ≤ X := by
    have hnlen : ((encode (normalizedInput F)).length : ℝ) ≤ (encode F).length :=
      Nat.cast_le.mpr (SubexpOrderedRawSparsify.normalized_length_le F)
    nlinarith
  have htimeX : (ExecEncodedSparsifier.runCost (localFrame c hr F middle) (arity c.T n)
      (SubexpConcreteNode.local_ready c hr _ hf) (SubexpConcreteNode.local_bank c hr _ _ hb)
      (arity_ge_two c.k c.T n) (normalizedInput F) : ℝ) ≤ 11 * X :=
    htime.trans (mul_le_mul_of_nonneg_left hEX (by norm_num))
  have hleafX : ((Encoding.encodeList encode
      (SubexpOrderedRawSparsify.output c hr F (M c n) (M_ge_two c n) middle hf hb)).length : ℝ) ≤
      2 * X := hleaf.trans (mul_le_mul_of_nonneg_left hEX (by norm_num))
  have hconst : (workRegs er : ℝ) + 39 ≤ ((workRegs er : ℝ) + 39) * X :=
    le_mul_of_one_le_right (by positivity) hX
  rw [bound_eq]
  push_cast
  have htotal : (3500 : ℝ) * (((encode F).length : ℝ) + 1) ^ 2 +
      15 * (encode (normalizedInput F)).length +
      ExecEncodedSparsifier.runCost (localFrame c hr F middle) (arity c.T n)
        (SubexpConcreteNode.local_ready c hr _ hf) (SubexpConcreteNode.local_bank c hr _ _ hb)
        (arity_ge_two c.k c.T n) (normalizedInput F) +
      6 * (Encoding.encodeList encode
        (SubexpOrderedRawSparsify.output c hr F (M c n) (M_ge_two c n) middle hf hb)).length +
      workRegs er + 39 ≤ ((workRegs er : ℝ) + 3577) * X := by nlinarith
  simpa only [X, E, mul_assoc] using htotal

/-- Concrete Main callback. All constraints refer to the same actual
caller, actual normalizer run and actual emitted ordered leaf stream. -/
theorem eventually_invoke (c : Config) {er : ℕ} (hr : 32 ≤ workRegs er) :
    ∀ᶠ n : ℕ in atTop, ∀ (F : ExecSparsifyObserved.Formula n),
      ExecSunflowerSearch.RawWidthAtMost c.k F →
      ∀ caller : MainState er (mainExtraStacks c), Prepared c n caller →
      caller.stacks (persistent (mainExtraStacks c) 0) = encode F →
      caller.stacks (persistent (mainExtraStacks c) 7) = [] →
      ∃ steps final leaves,
        Eval (procedure c hr).invoke steps caller final ∧
        (steps : ℝ) ≤ (workRegs er + 3577 : ℕ) * (((encode F).length : ℝ) + 1) ^ 2 *
          (2 : ℝ) ^ (130 * Statement.runtimeScale n) ∧
        SubexpOrderedRawSparsify.Outcome c F (M c n) caller final leaves ∧
        (leaves.length : ℝ) ≤ (2 : ℝ) ^ (129 * Statement.runtimeScale n) ∧
        ((Encoding.encodeList encode leaves).length : ℝ) ≤
          2 * (2 : ℝ) ^ (130 * Statement.runtimeScale n) := by
  filter_upwards [eventually_bound c hr,
    eventually_leaves_target c.k c.T c.width_ge_two c.control,
    eventually_encoded_leaves_target c.k c.T c.width_ge_two c.control] with n ht hl he
  intro F hF caller hp hbody hempty
  obtain ⟨middle,hf,hb,t,hbound,hrun,hout,hnorm⟩ :=
    SubexpOrderedRawSparsify.invoke_detailed c hr F hF (M c n) (M_ge_two c n)
      caller hbody hp.clean hempty hp.bank
  have hnorm_copy := hnorm
  obtain ⟨tn,_,en⟩ := hnorm_copy
  obtain ⟨hf',hb',_⟩ := normalized_frame c hr F hp hbody en
  have hready := ExecSparsifyStartup.normalizedInput_ready F c.k hF
  have hanti := ExecSparsifyStartup.normalizedInput_antichain F
  refine ⟨t,_,_,hrun,(Nat.cast_le.mpr hbound).trans (ht F hF caller middle hp hbody hnorm hf hb),hout,?_,?_⟩
  · exact hl (localFrame c hr F middle) hf' hb' (normalizedInput F) hready hanti
  · exact he (localFrame c hr F middle) hf' hb' (normalizedInput F) hready hanti

end SubexponentialSAT.SqrtLog.SparsifyProgram.Main

end OAI.Algorithms
