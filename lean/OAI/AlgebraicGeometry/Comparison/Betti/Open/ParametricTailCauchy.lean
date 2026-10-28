import OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricSeriesConvergence
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! # Parametric Tail Cauchy -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricTailCauchy.Dolbeault

noncomputable section

section

/-! Differentiation of the convergent actual mixed-jet tails over
neighborhoods contained in the compact parameter exhaustion. -/

open _root_.TopologicalSpace Set _root_.Metric Filter
open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

def openParametricTailJet (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (m k l : ℕ) (q : P × ℂ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => P) F :=
  ∑' n, MixedJetAlgebra.Dolbeault.mixedParameterJet (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg (n + m)) k l q

theorem openParametricTailJet_continuous (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (m k l : ℕ) :
    ContinuousOn (openParametricTailJet S g hg m k l)
      (interior (ParameterExhaustion.Dolbeault.openParameterCompact S m) ×ˢ ball (0 : ℂ) (m : ℝ)) :=
  ParametricSeriesConvergence.Dolbeault.correctedOpenParametricMixedJets_tail_continuous S g hg k l m

theorem hasFDerivAt_openParametricTailJet (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (m k l : ℕ)
    {q : P × ℂ} (hq : q ∈ interior (ParameterExhaustion.Dolbeault.openParameterCompact S m) ×ˢ ball (0 : ℂ) (m : ℝ)) :
    HasFDerivAt (openParametricTailJet S g hg m k l)
      (MixedJetDifferential.Dolbeault.mixedJetParameterDifferential (P := P) (F := F) k (openParametricTailJet S g hg m (k + 1) l q) +
        MixedJetDifferential.Dolbeault.mixedJetLineDifferential (P := P) (F := F) k (openParametricTailJet S g hg m k (l + 1) q)) q := by
  have h1 := (MixedJetDifferential.Dolbeault.mixedJetParameterDifferential (P := P) (F := F) k).uniformContinuous.comp_tendstoUniformlyOn
    (ParametricSeriesConvergence.Dolbeault.correctedOpenParametricMixedJets_tail_uniform S g hg (k + 1) l m m)
  have h2 := (MixedJetDifferential.Dolbeault.mixedJetLineDifferential (P := P) (F := F) k).uniformContinuous.comp_tendstoUniformlyOn
    (ParametricSeriesConvergence.Dolbeault.correctedOpenParametricMixedJets_tail_uniform S g hg k (l + 1) m m)
  have hD := (h1.add h2).mono (prod_mono interior_subset ball_subset_closedBall)
  apply hasFDerivAt_of_tendstoUniformlyOn
    (f := fun N x => ∑ n ∈ Finset.range N,
      MixedJetAlgebra.Dolbeault.mixedParameterJet (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg (n + m)) k l x)
    (isOpen_interior.prod isOpen_ball) hD ?_ ?_ hq
  · intro N x hx
    have hhol (n : ℕ) : ∀ p ∈ S, DifferentiableOn ℂ
        (fun z => ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg (n + m) (p, z)) (ball 0 (m : ℝ)) := by
      intro p hp
      exact (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference_holomorphic S g hg (n + m) hp).mono
        (ball_subset_closedBall.trans (closedBall_subset_closedBall (by push_cast; linarith)))
    have hN := HasFDerivAt.fun_sum (u := Finset.range N) (fun n _ =>
      MixedJetDifferential.Dolbeault.hasFDerivAt_mixedParameterJet_on (q := x) S.isOpen
        (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference_smooth S g hg (n + m)) isOpen_ball (hhol n) k l
        ⟨ParameterExhaustion.Dolbeault.openParameterCompact_subset S m (interior_subset hx.1), hx.2⟩)
    simpa only [Pi.add_apply, Function.comp_apply, map_sum, Finset.sum_add_distrib] using hN
  · intro x hx
    exact (ParametricSeriesConvergence.Dolbeault.correctedOpenParametricMixedJets_tail_uniform S g hg k l m m).tendsto_at
      ⟨interior_subset hx.1, ball_subset_closedBall hx.2⟩

end

section

/-! Joint smoothness of every summed mixed derivative tail on the
interiors of the actual compact parameter exhaustion sets. -/

open _root_.TopologicalSpace Set _root_.Metric
open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem openParametricTailJet_contDiffOn_nat (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (n m k l : ℕ) :
    ContDiffOn ℝ n (openParametricTailJet S g hg m k l)
      (interior (ParameterExhaustion.Dolbeault.openParameterCompact S m) ×ˢ ball (0 : ℂ) (m : ℝ)) := by
  induction n generalizing k l with
  | zero => exact contDiffOn_zero.mpr (openParametricTailJet_continuous S g hg m k l)
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      (isOpen_interior.prod isOpen_ball).uniqueDiffOn).mpr
    refine ⟨by simp, fun q =>
      MixedJetDifferential.Dolbeault.mixedJetParameterDifferential (P := P) (F := F) k (openParametricTailJet S g hg m (k + 1) l q) +
        MixedJetDifferential.Dolbeault.mixedJetLineDifferential (P := P) (F := F) k (openParametricTailJet S g hg m k (l + 1) q), ?_, ?_⟩
    · exact MixedJetDifferential.Dolbeault.mixedJetDifferential_contDiffOn k (ih (k + 1) l) (ih k (l + 1))
    · intro q hq
      exact (hasFDerivAt_openParametricTailJet S g hg m k l hq).hasFDerivWithinAt

theorem openParametricTailJet_smooth (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (m k l : ℕ) :
    ContDiffOn ℝ ∞ (openParametricTailJet S g hg m k l)
      (interior (ParameterExhaustion.Dolbeault.openParameterCompact S m) ×ˢ ball (0 : ℂ) (m : ℝ)) :=
  contDiffOn_infty.mpr (fun n => openParametricTailJet_contDiffOn_nat S g hg n m k l)

end

section

/-! Joint smoothness on the entire open parameter domain of the actual
corrected Cauchy series, decoded from its summed zero-order jet. -/

open _root_.TopologicalSpace Set _root_.Metric Filter
open scoped ContDiff _root_.Topology

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem openParametricTailJet_zero_value (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (m : ℕ) (q : P × ℂ) :
    (continuousMultilinearCurryFin0 ℝ P F) (openParametricTailJet S g hg m 0 0 q) =
      ∑' n, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg (n + m) q := by
  change (continuousMultilinearCurryFin0 ℝ P F).toContinuousLinearEquiv
    (∑' n, MixedJetAlgebra.Dolbeault.mixedParameterJet (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg (n + m)) 0 0 q) = _
  rw [ContinuousLinearEquiv.map_tsum]
  apply tsum_congr
  intro n
  rfl

theorem correctedOpenParametricCauchyTail_smooth (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (m : ℕ) :
    ContDiffOn ℝ ∞ (fun q => ∑' n, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg (n + m) q)
      (interior (ParameterExhaustion.Dolbeault.openParameterCompact S m) ×ˢ ball (0 : ℂ) (m : ℝ)) := by
  have h := (continuousMultilinearCurryFin0 ℝ P F).toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (openParametricTailJet_smooth S g hg m 0 0)
  apply h.congr
  intro q hq
  exact (openParametricTailJet_zero_value S g hg m q).symm

theorem correctedOpenParametricCauchySeries_smooth (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun q => ∑' n, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n q)
      ((S : Set P) ×ˢ univ) := by
  intro q hq
  obtain ⟨m, hm⟩ := ParameterExhaustion.Dolbeault.exists_openParameterCompact_product_neighborhood (q := q) S hq.1
  have he : (fun x => ∑' n, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n x) =ᶠ[𝓝 q]
      (fun x => (∑ n ∈ Finset.range m, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n x) +
        ∑' n, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg (n + m) x) := by
    filter_upwards [(S.isOpen.prod isOpen_univ).mem_nhds hq] with x hx
    exact ((ParametricSeriesConvergence.Dolbeault.correctedOpenParametricCauchyDifference_summable (q := x) S g hg hx.1).sum_add_tsum_nat_add m).symm
  have hp : ContDiffAt ℝ ∞
      (fun x => ∑ n ∈ Finset.range m, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n x) q :=
    (ContDiffOn.sum (fun n _ => ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference_smooth S g hg n)).contDiffAt
      ((S.isOpen.prod isOpen_univ).mem_nhds hq)
  have ht := (correctedOpenParametricCauchyTail_smooth S g hg m).contDiffAt
    ((isOpen_interior.prod isOpen_ball).mem_nhds hm)
  exact ((hp.add ht).congr_of_eventuallyEq he).contDiffWithinAt

theorem openParametricCauchyCandidate_smooth (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) :
    ContDiffOn ℝ ∞ (ParametricSeriesConvergence.Dolbeault.openParametricCauchyCandidate S g hg) ((S : Set P) ×ˢ univ) :=
  (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive_smoothOn S.isOpen hg 0).add
    (correctedOpenParametricCauchySeries_smooth S g hg)

end

section

/-! Holomorphic corrected tails and the actual antiholomorphic
derivative of the full series over an open parameter domain. -/

open _root_.TopologicalSpace Set _root_.Metric
open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem correctedOpenParametricCauchyDifference_dbar (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (n : ℕ) {p : P} (hp : p ∈ S) (z : ℂ) :
    VectorDbar.Dolbeault.vectorDbar (fun w => ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n (p, w)) z =
      VectorDbar.Dolbeault.vectorDbar (fun w => ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive g (n + 1) (p, w)) z -
        VectorDbar.Dolbeault.vectorDbar (fun w => ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive g n (p, w)) z := by
  have hD : DifferentiableAt ℝ (fun w => ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n (p, w)) z :=
    (ExpandingParametricPrimitives.Dolbeault.contDiff_slice_of_contDiffOn_product (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference_smoothOn S.isOpen hg n) hp).differentiable (by simp) z
  have hP := ParametricCauchyCorrections.Dolbeault.openParametricCauchyCorrectionPolynomial_entire S g hg n p z
  change VectorDbar.Dolbeault.vectorDbar (fun w => ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyDifference g n (p, w) -
    ParametricCauchyCorrections.Dolbeault.openParametricCauchyCorrectionPolynomial S g hg n (p, w)) z = _
  rw [CauchyHolomorphicLocus.Dolbeault.vectorDbar_sub hD (hP.restrictScalars ℝ), CauchyHolomorphicLocus.Dolbeault.vectorDbar_zero_of_holomorphic hP, sub_zero]
  change VectorDbar.Dolbeault.vectorDbar (fun w => ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive g (n + 1) (p, w) -
    ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive g n (p, w)) z = _
  exact CauchyHolomorphicLocus.Dolbeault.vectorDbar_sub
    ((ExpandingParametricPrimitives.Dolbeault.contDiff_slice_of_contDiffOn_product (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive_smoothOn S.isOpen hg (n + 1)) hp).differentiable (by simp) z)
    ((ExpandingParametricPrimitives.Dolbeault.contDiff_slice_of_contDiffOn_product (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive_smoothOn S.isOpen hg n) hp).differentiable (by simp) z)

theorem correctedOpenParametricCauchyTail_holomorphic (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (m : ℕ) {p : P} (hp : p ∈ ParameterExhaustion.Dolbeault.openParameterCompact S m) :
    DifferentiableOn ℂ (fun z => ∑' n, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg (n + m) (p, z))
      (ball 0 (m : ℝ)) := by
  apply Complex.differentiableOn_tsum_of_summable_norm
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1))
  · intro n
    exact (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference_holomorphic S g hg (n + m)
      (ParameterExhaustion.Dolbeault.openParameterCompact_subset S m hp)).mono
        (ball_subset_closedBall.trans (closedBall_subset_closedBall (by push_cast; linarith)))
  · exact isOpen_ball
  · intro n z hz
    have hmn : (m : ℝ) ≤ ((n + m : ℕ) : ℝ) := by push_cast; linarith
    have hb := CorrectedParametricJetBounds.Dolbeault.correctedOpenParametricCauchyDifference_bound S g hg (n + m) (q := (p, z))
      (ParameterExhaustion.Dolbeault.openParameterCompact_mono S (by omega : m ≤ n + m) hp)
      (closedBall_subset_closedBall hmn (ball_subset_closedBall hz))
    refine hb.trans ?_
    rw [show n + m + 1 = n + (m + 1) by omega, pow_add]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))

theorem correctedOpenParametricCauchySeries_dbar (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) (m : ℕ) {p : P} (hp : p ∈ ParameterExhaustion.Dolbeault.openParameterCompact S m)
    {z : ℂ} (hz : z ∈ ball 0 (m : ℝ)) :
    VectorDbar.Dolbeault.vectorDbar (fun w => ∑' n, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n (p, w)) z =
      ∑ n ∈ Finset.range m, VectorDbar.Dolbeault.vectorDbar (fun w => ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n (p, w)) z := by
  have hpS := ParameterExhaustion.Dolbeault.openParameterCompact_subset S m hp
  have ht := (correctedOpenParametricCauchyTail_holomorphic S g hg m hp).differentiableAt (isOpen_ball.mem_nhds hz)
  have he : (fun w => ∑' n, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n (p, w)) =
      (fun w => (∑ n ∈ Finset.range m, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n (p, w)) +
        ∑' n, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg (n + m) (p, w)) := by
    funext w
    exact ((ParametricSeriesConvergence.Dolbeault.correctedOpenParametricCauchyDifference_summable (q := (p, w)) S g hg hpS).sum_add_tsum_nat_add m).symm
  rw [he]
  have hf (n : ℕ) : ContDiff ℝ ∞ (fun w => ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n (p, w)) :=
    ExpandingParametricPrimitives.Dolbeault.contDiff_slice_of_contDiffOn_product (ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference_smooth S g hg n) hpS
  rw [CauchyHolomorphicLocus.Dolbeault.vectorDbar_add ((ContDiff.sum (fun n _ => hf n)).differentiable (by simp) z)
    (ht.restrictScalars ℝ), CauchyHolomorphicLocus.Dolbeault.vectorDbar_zero_of_holomorphic ht, add_zero]
  exact CauchyHolomorphicLocus.Dolbeault.vectorDbar_sum _ (fun n _ => (hf n).differentiable (by simp) z)

end

/-! A global primitive in the entire complex-line variable, jointly
smooth over an arbitrary open finite-dimensional complex parameter domain. -/

open _root_.TopologicalSpace Set _root_.Metric
open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem openParametricCauchyCandidate_dbar (S : Opens P) (g : P × ℂ → F)
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) {p : P} (hp : p ∈ S) (z : ℂ) :
    VectorDbar.Dolbeault.vectorDbar (fun w => ParametricSeriesConvergence.Dolbeault.openParametricCauchyCandidate S g hg (p, w)) z = g (p, z) := by
  obtain ⟨m, hpm, hz⟩ := ParameterExhaustion.Dolbeault.exists_openParameterCompact_product_neighborhood (q := (p, z)) S hp
  have h0 : DifferentiableAt ℝ (fun w => ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive g 0 (p, w)) z :=
    (ExpandingParametricPrimitives.Dolbeault.contDiff_slice_of_contDiffOn_product (ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive_smoothOn S.isOpen hg 0) hp).differentiable (by simp) z
  have hs : DifferentiableAt ℝ (fun w => ∑' n, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n (p, w)) z :=
    (ExpandingParametricPrimitives.Dolbeault.contDiff_slice_of_contDiffOn_product (correctedOpenParametricCauchySeries_smooth S g hg) hp).differentiable (by simp) z
  change VectorDbar.Dolbeault.vectorDbar (fun w => ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive g 0 (p, w) +
    ∑' n, ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n (p, w)) z = _
  rw [CauchyHolomorphicLocus.Dolbeault.vectorDbar_add h0 hs, correctedOpenParametricCauchySeries_dbar S g hg m (interior_subset hpm) hz]
  have htel : (∑ n ∈ Finset.range m,
      VectorDbar.Dolbeault.vectorDbar (fun w => ParametricCauchyCorrections.Dolbeault.correctedOpenParametricCauchyDifference S g hg n (p, w)) z) =
      VectorDbar.Dolbeault.vectorDbar (fun w => ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive g m (p, w)) z -
        VectorDbar.Dolbeault.vectorDbar (fun w => ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive g 0 (p, w)) z := by
    calc
      _ = ∑ n ∈ Finset.range m,
          (VectorDbar.Dolbeault.vectorDbar (fun w => ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive g (n + 1) (p, w)) z -
            VectorDbar.Dolbeault.vectorDbar (fun w => ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive g n (p, w)) z) :=
        Finset.sum_congr rfl (fun n _ => correctedOpenParametricCauchyDifference_dbar S g hg n hp z)
      _ = _ := Finset.sum_range_sub
        (fun n => VectorDbar.Dolbeault.vectorDbar (fun w => ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive g n (p, w)) z) m
  rw [htel, ExpandingParametricPrimitives.Dolbeault.expandingParametricCauchyPrimitive_dbar_on hg m hp
    (closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hz))]
  abel

theorem exists_open_parametric_vectorDbar_primitive (S : Opens P) {g : P × ℂ → F}
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ univ)) :
    ∃ G : P × ℂ → F, ContDiffOn ℝ ∞ G ((S : Set P) ×ˢ univ) ∧
      ∀ p ∈ S, ∀ z : ℂ, VectorDbar.Dolbeault.vectorDbar (fun w => G (p, w)) z = g (p, z) :=
  ⟨ParametricSeriesConvergence.Dolbeault.openParametricCauchyCandidate S g hg, openParametricCauchyCandidate_smooth S g hg,
    fun _ hp z => openParametricCauchyCandidate_dbar S g hg hp z⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.ParametricTailCauchy.Dolbeault
