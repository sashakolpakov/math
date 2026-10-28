import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SetupComplete
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawPrefix
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyObserved

namespace OAI.Algorithms

/-! Actual ordered-input frontend followed by the complete new numerical
setup. Constants and polynomial degree are fixed before the input formula. -/

namespace SubexponentialSAT.SqrtLog.Execution

open BitProgram StructuredCalls SubexpMainProgram
open SubexpSetupProgram (Config mainExtraStacks SetupState)
open SubexpSetupStorage (WordBound)

structure SetupRun (c : Config) (er : ℕ) {n : ℕ}
    (F : SubexpOrderedRawPrefix.Formula n) where
  before : MainState er (mainExtraStacks c)
  out : SetupState c
  prefixSteps : ℕ
  setupSteps : ℕ
  prefixTrace : Eval (frontendProcedure er (mainExtraStacks c)).invoke prefixSteps
    (initialData er (mainExtraStacks c) (SubexpOrderedRawPrefix.encode F)) before
  setupTrace : Eval (Setup.Complete.procedure c er).invoke setupSteps before
    ((Setup.Complete.procedure c er).install before out)
  facts : SubexpOrderedRawPrefix.Facts F before
  values : Setup.Complete.Values c n out
  frame : ∀ i : Fin 32, i ≠ 4 → i ≠ 23 → i ≠ 24 → i ≠ 30 → i ≠ 31 →
    ((Setup.Complete.procedure c er).install before out).stacks
      (persistent (mainExtraStacks c) i) = before.stacks (persistent (mainExtraStacks c) i)

noncomputable def SetupRun.afterSetup {c : Config} {er n : ℕ} {F : SubexpOrderedRawPrefix.Formula n}
    (r : SetupRun c er F) : MainState er (mainExtraStacks c) :=
  (Setup.Complete.procedure c er).install r.before r.out

theorem SetupRun.body {c : Config} {er n : ℕ} {F : SubexpOrderedRawPrefix.Formula n}
    (r : SetupRun c er F) :
    r.afterSetup.stacks (persistent (mainExtraStacks c) 0) = ExecSparsifyObserved.encode F := by
  rw [SetupRun.afterSetup, r.frame 0 (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact r.facts.body

theorem SetupRun.empty {c : Config} {er n : ℕ} {F : SubexpOrderedRawPrefix.Formula n}
    (r : SetupRun c er F) (i : Fin 32) (hi : 6 ≤ i.val)
    (h23 : i ≠ 23) (h24 : i ≠ 24) (h30 : i ≠ 30) (h31 : i ≠ 31) :
    r.afterSetup.stacks (persistent (mainExtraStacks c) i) = [] := by
  have h4 : i ≠ 4 := by
    intro h
    have hv := congrArg (fun j : Fin 32 => j.val) h
    change i.val = 4 at hv
    omega
  exact (r.frame i h4 h23 h24 h30 h31).trans (r.facts.empty i hi)

/-- No sufficiently-large-input premise is needed for the frontend and
numerical setup. The old frontend's temporary scale is physically replaced. -/
theorem setup_runs (c : Config) (er : ℕ) :
    ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧
      ∀ n (F : SubexpOrderedRawPrefix.Formula n),
        ∃ r : SetupRun c er F,
          r.prefixSteps + r.setupSteps ≤ C * (SubexpOrderedRawPrefix.bitLength F + 1)^q := by
  obtain ⟨C,q,hC,hq,hsetup⟩ := Setup.Complete.procedure_bounded_eval c
  refine ⟨133+C*135^q, 2*q, by omega, by omega, ?_⟩
  intro n F
  let L := SubexpOrderedRawPrefix.bitLength F
  let M := L + SubexpFrontendPrefix.bound L
  obtain ⟨nb,sb,ub,tp,hn,hs,hu,hp,ep⟩ :=
    SubexpOrderedRawPrefix.prefix_execution er (mainExtraStacks c) F
  let before := prefixData er (mainExtraStacks c) (SubexpOrderedRawPrefix.encode F)
    (SubexpOrderedRawPrefix.body F) nb sb ub
  have hinit : WordBound L (initialData er (mainExtraStacks c) (SubexpOrderedRawPrefix.encode F)) :=
    SubexpSetupMainRuntime.initial_wordBound er (mainExtraStacks c) (SubexpOrderedRawPrefix.encode F)
  have hbefore : WordBound M before := SubexpSetupBoundSpec.wordBound_mono
    (SubexpSetupBoundSpec.eval_wordBound hinit ep) (Nat.add_le_add_left hp L)
  obtain ⟨ts,out,es,ht,_,hv,hf⟩ := hsetup er M before hbefore
  have facts : SubexpOrderedRawPrefix.Facts F before :=
    SubexpOrderedRawPrefix.prefix_facts er (mainExtraStacks c) F nb sb ub hn hs hu
  have values : Setup.Complete.Values c n out := by
    simpa only [facts.variableCount] using hv
  let r : SetupRun c er F := ⟨before,out,tp,ts,ep,es,facts,values,hf⟩
  refine ⟨r, ?_⟩
  change tp+ts ≤ (133+C*135^q)*(L+1)^(2*q)
  have hgrowth : M+1 ≤ 135*(L+1)^2 := SubexpSetupMainRuntime.prefix_growth_polynomial L
  have hsbound : C*(M+1)^q ≤ C*135^q*(L+1)^(2*q) := by
    calc
      _ ≤ C*(135*(L+1)^2)^q := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hgrowth q)
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  have hpow : (L+1)^2 ≤ (L+1)^(2*q) := Nat.pow_le_pow_right (by omega) (by omega)
  have hpbound : tp ≤ 133*(L+1)^(2*q) :=
    hp.trans ((SubexpSetupMainRuntime.prefix_bound_polynomial L).trans (Nat.mul_le_mul_left _ hpow))
  calc
    _ ≤ 133*(L+1)^(2*q)+C*135^q*(L+1)^(2*q) := Nat.add_le_add hpbound (ht.trans hsbound)
    _ = _ := by ring

end SubexponentialSAT.SqrtLog.Execution

end OAI.Algorithms
