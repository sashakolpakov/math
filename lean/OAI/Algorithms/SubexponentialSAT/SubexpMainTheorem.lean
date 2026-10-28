import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainBackendBounds

namespace OAI.Algorithms

/-! The fixed finite program, its bounded leaf executions, and the actual
controller yield the manuscript's main asymptotic SAT statement. -/

namespace SubexponentialSAT.SubexpMainTheorem

open Filter SubexpMainProgram SubexpSetupProgram SubexpPackingParameters SubexpComputation

local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

theorem feasible (cfg : Config) (hsize : 672 ≤ helperSize cfg) : Feasible cfg.k := by
  let er : ℕ := 16
  have hregs : 16 ≤ er := le_rfl
  let hboot : 32 ≤ workRegs er := SubexpMainFixedProgram.enough_registers er hregs
  let phases := SubexpMainFixedProgram.phases cfg hsize er hregs
  obtain ⟨C0, d0, hC0, hd0, hinitial⟩ := SubexpMainInitialState.eventually_run cfg hboot
  obtain ⟨CN, dN, hCN, hrecords⟩ := SubexpMainBootBounds.records_bound cfg hboot
  let C : ℝ := (C0 + CN : ℕ) + SubexpMainBackendBounds.coefficient + 1
  let A : ℝ := SubexpMainBackendBounds.exponent + 3
  let d : ℕ := d0 + dN + SubexpMainBackendBounds.degree cfg.k d0 + 1
  have hbC := SubexpMainBackendBounds.coefficient_ge_one
  have hbA := SubexpMainBackendBounds.exponent_ge_one
  have hC0r : (0 : ℝ) ≤ C0 := Nat.cast_nonneg _
  have hCNr : (0 : ℝ) ≤ CN := Nat.cast_nonneg _
  have hC : 1 ≤ C := by dsimp [C]; push_cast; linarith
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hCboot : (C0 : ℝ) ≤ C := by dsimp [C]; push_cast; linarith
  have hCcount : (CN : ℝ) ≤ C := by dsimp [C]; push_cast; linarith
  have hCback : SubexpMainBackendBounds.coefficient ≤ C := by
    dsimp [C]; push_cast; linarith
  have hAboot : (3 : ℝ) ≤ A := by dsimp [A]; linarith
  have hAcount : (2 : ℝ) ≤ A := by dsimp [A]; linarith
  have hAback : SubexpMainBackendBounds.exponent ≤ A := by dsimp [A]; linarith
  have hdboot : d0 ≤ d := by dsimp [d]; omega
  have hdcount : dN ≤ d := by dsimp [d]; omega
  have hdback : SubexpMainBackendBounds.degree cfg.k d0 ≤ d := by dsimp [d]; omega
  apply SubexpMainController.feasible_of_executions phases
    (SubexpEmptyClauseGuard.leafCallback phases) cfg.k
    (constant := SubexpMainMeasuredBound.constant cfg er C)
    (exponentConstant := SubexpMainMeasuredBound.exponent A)
    (degree := SubexpMainMeasuredBound.degree cfg d)
  · have hk : 1 ≤ SubexpMainMeasuredBound.baseConstant cfg er C := by
      have hn := Nat.cast_nonneg (α := ℝ) (8*cfg.k+5+helperSize cfg+workRegs er+1)
      unfold SubexpMainMeasuredBound.baseConstant
      linarith
    have hsq : 1 ≤ (SubexpMainMeasuredBound.baseConstant cfg er C)^2 := one_le_pow₀ hk
    have hq : 1 ≤ 50003*(SubexpMainMeasuredBound.baseConstant cfg er C)^2 := by nlinarith
    have hq2 : 1 ≤ (50003*(SubexpMainMeasuredBound.baseConstant cfg er C)^2)^2 := one_le_pow₀ hq
    unfold SubexpMainMeasuredBound.constant
    nlinarith
  · unfold SubexpMainMeasuredBound.exponent
    positivity
  · unfold SubexpMainMeasuredBound.degree SubexpMainMeasuredBound.baseDegree
    omega
  · filter_upwards [hinitial,
      SubexpMainBackendBounds.eventually_prefix cfg er hboot hsize hregs C0 d0,
      DyadicSchedule.eventually_ready cfg.k cfg.T cfg.width_ge_two] with n hinit hbackend ready
    intro F hF
    have good := DyadicSchedule.ready_goodInput ready
    let _ : NeZero (r n) := ⟨Nat.ne_of_gt (goodInput_s_pos good)⟩
    obtain ⟨boot, htime, hinvariant, hcache, hwords⟩ := hinit F hF
    let L := Encoding.formulaBitLength F
    let budget := SubexpMainPrefixBudget.limit C A d L n
    let invariant : MainState er (mainExtraStacks cfg) → Prop :=
      SubexpMainInvariant.Invariant cfg boot.setupOutput (C0*(L+1)^d0)
    have provider : SubexpLeafContract.StageProvider
        (k := cfg.k) (Δ := DyadicSchedule.delta cfg.k cfg.T n)
        (r := r n) (tau := DyadicSchedule.tau n)
        phases (helperSize cfg) (SubexpMainInvariant.helper_within cfg)
        (ell_pos good) (p_lower good).le (SubexpMainAssembly.validLeaf cfg n) invariant budget := by
      apply SubexpMainInvariant.stage_provider
      intro G valid hne tail base hbase
      obtain ⟨backend⟩ := SubexpMainBackend.transferred_run_exists
        (hregs := hregs) hsize boot ready base hbase valid hne tail hcache
      have hb := hbackend F boot base G tail hbase hwords valid _ ready backend
      have hb' := hb.trans (SubexpMainMeasuredBound.monotone
        (le_trans (by norm_num) hbC) hCback hAback hdback L n)
      refine ⟨SubexpMainScheduledLayout.parameters cfg n ready,
        backend.original, backend.stages, ?_, backend.stored⟩
      exact SubexpMainPrefixBudget.of_le (ExecQuantitativeSparsify.encodeRawFormula G) hb'
    have hn : 0 < n := by have := goodInput_two_le good; omega
    let run := SubexpMainAssembly.execution boot phases rfl rfl (helperSize cfg)
      (SubexpMainInvariant.helper_within cfg) (by omega : 9 ≤ helperSize cfg) rfl
      (ell_pos good) (p_lower good).le hn invariant budget hinvariant
      (fun base hb => SubexpMainInvariant.ready hb) provider
    have htime' := htime.trans (SubexpMainMeasuredBound.monotone
      hC0r hCboot hAboot hdboot L n)
    have hcount' := (hrecords n good F hF boot).trans (SubexpMainMeasuredBound.monotone
      hCNr hCcount hAcount hdcount L n)
    refine ⟨run, ?_⟩
    change ((SubexpMainBootBounds.totalSteps boot + 5 + RecordPrograms.budget
      (SubexpMainAssembly.leafCost er (helperSize cfg) n (ell n) (p n) budget)
      boot.records : ℕ) : ℝ) ≤ _
    exact SubexpMainMeasuredBound.measured_bound boot hC hA good htime' hcount'

theorem mainTheorem : SubexpComputation.MainTheorem := by
  intro k hk
  obtain ⟨cfg, hwidth, hsize⟩ := SubexpMainFixedProgram.configuration_exists k (by omega)
  rw [← hwidth]
  exact feasible cfg hsize

end SubexponentialSAT.SubexpMainTheorem

end OAI.Algorithms
