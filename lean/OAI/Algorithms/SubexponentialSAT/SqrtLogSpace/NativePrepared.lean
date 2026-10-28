import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeSetupSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CanonicalFrontend
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSStartup
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit

/-! The actual canonical setup frame supplies the exact disjoint DFS ports.
No declared coordinate is compressed, and the threshold is the computed
reciprocal-budget choice used by the sharp visit bound. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls BinaryArithmetic DisjointReuse

theorem SetupReady.dfs_prepared {k n : ℕ} {F : SAT.CNF (Fin n)}
    {a : State 80 1220} (h : SetupReady k F a) :
    DFSStartup.Prepared (a.stacks 259)
      (ExecCNF.normalize SAT.Literal.negate (ExecQuantitativeSparsify.formulaList F)) a := by
  refine ⟨h.blank 257 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), h.header, rfl,
    h.blank 260 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    h.blank 261 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    h.blank 262 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    h.blank 263 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    h.body.trans (canonical_normalized_body F), ?_⟩
  intro i hi
  apply h.blank i
  · intro he
    subst i
    change 256 < 256 at hi
    omega
  all_goals intro he; subst i; omega

theorem SetupReady.dfs_threshold {k n : ℕ} {F : SAT.CNF (Fin n)}
    {a : State 80 1220} (h : SetupReady k F a) (hs : 0 < sparsifySchedule n)
    (hσ : (0 : ℚ) < 1 / sparsifySchedule n) :
    2 ≤ toNat (a.stacks 259) ∧
      toNat (a.stacks 259) = SparseBudget.chooseForSigma k (1 / sparsifySchedule n) hσ := by
  rw [h.threshold]
  exact ⟨(SparseBudget.chooseM_spec k 1 (sparsifySchedule n) (by decide)).1,
    (SparseBudget.chooseForSigma_reciprocal k (sparsifySchedule n) hs hσ).symm⟩

/-- The prepared frame is produced by the measured setup command itself.
The retained `SetupReady` fields give its exact numeric ambient and occurrence
words, rather than assumptions about an externally supplied layout. -/
theorem setup_prepared_execution (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ {n : ℕ} (F : SAT.CNF (Fin n)), 20 ≤ n →
      0 < sparsifySchedule n → ∃ steps b,
        DFSVisit.BoundedEval (setupCommand k) steps (StructuredProgram.ioState ABI.countStack
          (Encoding.encodeCNF F)) b ((C + 1) * (Encoding.formulaBitLength F + 1) ^ 3) ∧
        DFSStartup.Prepared (b.stacks 259)
          (ExecCNF.normalize SAT.Literal.negate (ExecQuantitativeSparsify.formulaList F)) b ∧
        SetupReady k F b ∧ steps + 1 ≤ C * (Encoding.formulaBitLength F + 1) ^ 3 := by
  obtain ⟨C, hC, hrun⟩ := setup_eval k hk
  refine ⟨C, hC, ?_⟩
  intro n F hn hs
  obtain ⟨steps, b, he, hb, ht⟩ := hrun F hn hs
  refine ⟨steps, b, ⟨he, ?_⟩, hb.dfs_prepared, hb, ht⟩
  intro t c hle htrace i
  have hinitial : dataBits
      ((StructuredProgram.ioState (r := 80) ABI.countStack (Encoding.encodeCNF F)).withPC
        (some (compiled (setupCommand k) 256 256).entry)) ≤ Encoding.formulaBitLength F := by
    change dataBits (initial (compiled (setupCommand k) 256 256) (Encoding.encodeCNF F)) ≤ _
    rw [initial_dataBits]
    exact le_rfl
  have hlocal := StructuredSpace.local_stack_bound (compiled (setupCommand k) 256 256)
    (steps := C * (Encoding.formulaBitLength F + 1) ^ 3) hinitial t c
    (hle.trans ((Nat.le_succ steps).trans ht)) htrace i
  have hlinear : Encoding.formulaBitLength F ≤ (Encoding.formulaBitLength F + 1) ^ 3 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  nlinarith only [hlocal, hlinear]

/-- The large branch can reuse the actual parsed frame after the finite cutoff
test, without reparsing or assuming the remaining setup has been executed. -/
theorem setupAfterFrontend_prepared_execution (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ {n : ℕ} (F : SAT.CNF (Fin n))
      (binary : List Bool) (a : State 80 1220),
      FrontendReady F binary a → toNat binary = n → binary.length ≤ n →
      20 ≤ n → 0 < sparsifySchedule n → ∃ steps b,
        DFSVisit.BoundedEval (setupAfterFrontend k) steps a b
          ((C + 1220) * (Encoding.formulaBitLength F + 1) ^ 3) ∧
        DFSStartup.Prepared (b.stacks 259)
          (ExecCNF.normalize SAT.Literal.negate (ExecQuantitativeSparsify.formulaList F)) b ∧
        SetupReady k F b ∧ steps + 1 ≤ C * (Encoding.formulaBitLength F + 1) ^ 3 := by
  obtain ⟨C, hC, hrun⟩ := setupAfterFrontend_eval k hk
  refine ⟨C, hC, ?_⟩
  intro n F binary a ha hv hlen hn hs
  obtain ⟨steps, b, he, hb, ht⟩ := hrun F binary a ha hv hlen hn hs
  refine ⟨steps, b, ⟨he, ?_⟩, hb.dfs_prepared, hb, ht⟩
  intro t c hle htrace i
  have hinitial := StreamResources.dataBits_le_mul
    (a.withPC (some (compiled (setupAfterFrontend k) 256 256).entry))
    (frontendReady_stack_bound F binary a ha hlen)
  have hlocal := StructuredSpace.local_stack_bound (compiled (setupAfterFrontend k) 256 256)
    (steps := C * (Encoding.formulaBitLength F + 1) ^ 3) hinitial t c
    (hle.trans ((Nat.le_succ steps).trans ht)) htrace i
  have hlinear : Encoding.formulaBitLength F + 1 ≤ (Encoding.formulaBitLength F + 1) ^ 3 :=
    Nat.le_self_pow (by decide) _
  nlinarith only [hlocal, hlinear]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
