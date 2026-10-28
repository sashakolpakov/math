import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HigherCutoffRegularity
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffExistence
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffIdentities

/-! # Local Smooth Regularity -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalSmoothRegularity.CM.Construction

noncomputable section

section

/-! Interior smoothness of actual weak solutions, by nested cutoff induction
through every Sobolev order and the genuine Fourier smoothness theorem. -/

open _root_.MeasureTheory TemperedDistribution Set
open scoped SchwartzMap ContDiff _root_.Topology

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

def IsLocalEuclideanWeakMetricSolution (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι) (U : Set E)
    (u f : Lp ℂ 2 (volume : Measure E)) : Prop :=
  ∀ g : 𝓢(E, ℂ), HasCompactSupport (g : E → ℂ) →
    (∀ x, g x = Complex.ofReal (g x).re) → tsupport g ⊆ U →
    ∀ v : Lp ℂ 2 (volume : Measure E),
      (∫ x, inner ℝ (A x (EuclideanGradient.CM.Construction.sobolevVectorGradient b u x))
        (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v) x)) =
        inner ℝ f (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v))

theorem local_elliptic_all_orders (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (c : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport (fun x => A x - c))
    {L : NNReal} (hL : LipschitzWith L A) {C a : ℝ}
    (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a)
    (hpos : ∀ x, ∀ w : EuclideanSpace ℂ ι, a * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w)
    {U : Set E} (hU : IsOpen U) (u f : Lp ℂ 2 (volume : Measure E))
    (hsol : IsLocalEuclideanWeakMetricSolution b A U u f)
    (hf : ∀ n : ℕ, MemSobolev (n : ℝ) 2 (f : 𝓢'(E, ℂ)))
    (n : ℕ) (g : 𝓢(E, ℂ)) (hgc : HasCompactSupport (g : E → ℂ))
    (hgreal : ∀ x, g x = Complex.ofReal (g x).re) (hgU : tsupport g ⊆ U) :
    MemSobolev ((n : ℝ) + 1) 2 (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
      (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u) : 𝓢'(E, ℂ)) := by
  induction n generalizing g with
  | zero =>
    simp only [Nat.cast_zero, zero_add]
    rw [SobolevIs.CM.Construction.sobolevL2Embedding_distribution, memSobolev_besselPotential_iff, neg_add_cancel]
    exact memSobolev_zero_iff.mpr ⟨SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u, rfl⟩
  | succ n ih =>
    obtain ⟨η, hηc, hηU, hηreal, hηg⟩ := NestedCutoffExistence.CM.Construction.exists_real_schwartz_cutoff_near_compact hgc hU hgU
    have hηreg := ih η hηc hηreal hηU
    have hlocal (v : Lp ℂ 2 (volume : Measure E)) :
        (∫ x, inner ℝ (A x (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 η u) x))
          (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v) x)) =
          inner ℝ f (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v)) :=
      (NestedCutoffIdentities.CM.Construction.nested_cutoff_energy_eq b A g η hηg u v).trans (hsol g hgc hgreal hgU v)
    have hreg := HigherCutoffRegularity.CM.Construction.local_elliptic_cutoff_regularity b n A c hA hc hL hC ha hpos g hgreal
      (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 η u) f hlocal hηreg (hf n)
    rw [NestedCutoffIdentities.CM.Construction.sobolevCutoffCLM_nested 1 g η hηg u] at hreg
    simpa only [Nat.cast_succ, add_assoc, one_add_one_eq_two] using hreg

theorem local_elliptic_smooth_near_point (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (c : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport (fun x => A x - c))
    {L : NNReal} (hL : LipschitzWith L A) {C a : ℝ}
    (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a)
    (hpos : ∀ x, ∀ w : EuclideanSpace ℂ ι, a * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w)
    {U : Set E} (hU : IsOpen U) (u f : Lp ℂ 2 (volume : Measure E))
    (hsol : IsLocalEuclideanWeakMetricSolution b A U u f)
    (hf : ∀ n : ℕ, MemSobolev (n : ℝ) 2 (f : 𝓢'(E, ℂ))) {x : E} (hx : x ∈ U) :
    ∃ g : 𝓢(E, ℂ), (g : E → ℂ) =ᶠ[𝓝 x] 1 ∧
      ∃ v : BoundedContinuousFunction E ℂ,
        SobolevInv.CM.Construction.boundedFunctionDistribution v = (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
          (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u) : 𝓢'(E, ℂ)) ∧ ContDiff ℝ (⊤ : ℕ∞) (v : E → ℂ) := by
  obtain ⟨g, hgc, hgU, hgreal, hgx⟩ := NestedCutoffExistence.CM.Construction.exists_real_schwartz_cutoff_near_compact
    (isCompact_singleton (x := x)) hU (singleton_subset_iff.mpr hx)
  refine ⟨g, hgx x (mem_singleton x), ?_⟩
  apply Smooth.CM.Construction.sobolev_all_orders_smooth
  intro n
  exact (local_elliptic_all_orders b A c hA hc hL hC ha hpos hU u f hsol hf
    n g hgc hgreal hgU).mono (by linarith)

end

/-! Compact smooth test equations extend to the completed local H1 test
space by boundedness of the actual metric energy and Schwartz density. -/

open _root_.MeasureTheory Set
open scoped SchwartzMap

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

theorem localWeakMetricSolution_of_schwartz_tests (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hAm : AEStronglyMeasurable A volume) {B : ℝ} (hAB : ∀ᵐ x ∂volume, ‖A x‖ ≤ B)
    (U : Set E) (u f : Lp ℂ 2 (volume : Measure E))
    (hsol : ∀ g : 𝓢(E, ℂ), HasCompactSupport (g : E → ℂ) → tsupport g ⊆ U →
      (∫ x, inner ℝ (A x (EuclideanGradient.CM.Construction.sobolevVectorGradient b u x))
        (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 g) x)) = inner ℝ f (g.toLp 2)) :
    IsLocalEuclideanWeakMetricSolution b A U u f := by
  intro g hgc _hgreal hgU v
  let S := SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g
  let L : Lp ℂ 2 (volume : Measure E) →L[ℝ] ℝ :=
    (CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hAm hAB (EuclideanGradient.CM.Construction.sobolevVectorGradient b u)).comp
      (((EuclideanGradient.CM.Construction.sobolevVectorGradient b).comp S).restrictScalars ℝ)
  let R : Lp ℂ 2 (volume : Measure E) →L[ℝ] ℝ :=
    (innerSL ℝ f).comp (((SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)).comp S).restrictScalars ℝ)
  have hLR : (L : Lp ℂ 2 (volume : Measure E) → ℝ) = R :=
    (SobolevSmoothDensity.CM.Construction.schwartzSobolevCoordinate_denseRange (E := E) 1).equalizer L.continuous R.continuous (by
      funext φ
      let q := SchwartzMap.smulLeftCLM ℂ g φ
      have hq : tsupport q ⊆ tsupport g :=
        closure_minimal ((SobolevIs.CM.Construction.supportedSchwartzSubmodule_mem_iff _ _).mp
          (SobolevSmoothDensity.CM.Construction.schwartz_cutoff_mem_supported g φ (subset_tsupport g))) (isClosed_tsupport _)
      have hqc : HasCompactSupport (q : E → ℂ) :=
        hgc.of_isClosed_subset (isClosed_tsupport _) hq
      change CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hAm hAB (EuclideanGradient.CM.Construction.sobolevVectorGradient b u)
        (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 φ))) =
          inner ℝ f (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
            (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 φ)))
      have hcut := SobolevSmoothDensity.CM.Construction.sobolevCutoffCLM_schwartz 1 g φ
      norm_num only [Nat.cast_one] at hcut
      rw [hcut, SobolevIs.CM.Construction.sobolevL2Embedding_schwartz, CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply]
      exact hsol q hqc (hq.trans hgU))
  have h := congrFun hLR v
  change CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hAm hAB (EuclideanGradient.CM.Construction.sobolevVectorGradient b u)
    (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v)) = _ at h
  rwa [CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply] at h

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalSmoothRegularity.CM.Construction
