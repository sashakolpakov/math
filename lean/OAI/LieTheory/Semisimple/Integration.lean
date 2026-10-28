import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Integration -/

namespace OAI.LieTheory.Semisimple.Integration.Constructions.CharacterTriviality

/-! Compact parameter integrals used to regularize the character in CharacterTriviality. -/

open Set Filter _root_.Metric _root_.MeasureTheory
open scoped _root_.Manifold ContDiff _root_.Topology

variable {P F X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

theorem hasFDerivAt_integral_compact
    {f : P → X → F} {f' : P → X → P →L[ℝ] F}
    {U : Set P} {K : Set X} (hU : IsOpen U) (hK : IsCompact K)
    (hKm : MeasurableSet K) {x : P} (hx : x ∈ U)
    (hf : ContinuousOn (Function.uncurry f) (U ×ˢ K))
    (hf' : ContinuousOn (Function.uncurry f') (U ×ˢ K))
    (hd : ∀ p ∈ U, ∀ y ∈ K, HasFDerivAt (fun z => f z y) (f' p y) p) :
    HasFDerivAt (fun p => ∫ y in K, f p y ∂μ) (∫ y in K, f' x y ∂μ) x := by
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x r).prod hK).exists_bound_of_continuousOn
    (hf'.mono (prod_mono hball Subset.rfl))
  have hfc (p : P) (hp : p ∈ U) : ContinuousOn (f p) K :=
    hf.comp (continuous_const.prodMk continuous_id).continuousOn (fun y hy => ⟨hp, hy⟩)
  have hfc' : ContinuousOn (f' x) K :=
    hf'.comp (continuous_const.prodMk continuous_id).continuousOn (fun y hy => ⟨hx, hy⟩)
  have hfinite : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := μ.restrict K) (s := ball x r) (bound := fun _ => C)
    (ball_mem_nhds x hr)
    (by
      filter_upwards [hU.mem_nhds hx] with p hp
      exact (hfc p hp).aestronglyMeasurable hKm)
    ((hfc x hx).integrableOn_compact hK)
    (hfc'.aestronglyMeasurable hKm)
    (by
      filter_upwards [ae_restrict_mem hKm] with y hy p hp
      exact hC (p, y) ⟨ball_subset_closedBall hp, hy⟩)
    (integrable_const C)
    (by
      filter_upwards [ae_restrict_mem hKm] with y hy p hp
      exact hd p (hball (ball_subset_closedBall hp)) y hy))

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [ChartedSpace H X] [IsManifold (𝓘(ℝ, H)) ∞ X]

omit [FiniteDimensional ℝ P] [T2Space X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] in
theorem contMDiffOn_partialFDeriv
    {k : P × X → F} {U : Set P} (hU : IsOpen U)
    (hk : ContMDiffOn ((𝓘(ℝ, P)).prod (𝓘(ℝ, H))) (𝓘(ℝ, F)) ∞ k (U ×ˢ univ)) :
    ContMDiffOn ((𝓘(ℝ, P)).prod (𝓘(ℝ, H))) (𝓘(ℝ, P →L[ℝ] F)) ∞
      (fun p => fderiv ℝ (fun z => k (z, p.2)) p.1) (U ×ˢ univ) := by
  intro p hp
  have hkp : ContMDiffAt (((𝓘(ℝ, P)).prod (𝓘(ℝ, H))).prod (𝓘(ℝ, P)))
      (𝓘(ℝ, F)) ∞ (fun q : (P × X) × P => k (q.2, q.1.2)) (p, p.1) :=
    ((hk p hp).contMDiffAt ((hU.prod isOpen_univ).mem_nhds hp)).comp (p, p.1)
      (contMDiffAt_snd.prodMk (contMDiffAt_snd.comp _ contMDiffAt_fst))
  have hder := hkp.mfderiv (fun (p : P × X) (z : P) => k (z, p.2))
    (fun (p : P × X) => p.1)
    contMDiffAt_fst (m := ∞) (by simp)
  simp only [inTangentCoordinates_model_space, mfderiv_eq_fderiv] at hder
  exact hder.contMDiffWithinAt

theorem hasFDerivAt_weightedIntegral
    {k : P × X → ℂ} {U : Set P} {K : Set X} (hU : IsOpen U) (hK : IsCompact K)
    (hk : ContMDiffOn ((𝓘(ℝ, P)).prod (𝓘(ℝ, H))) (𝓘(ℝ, ℂ)) ∞ k (U ×ˢ univ))
    {w : X → ℂ} (hw : Continuous w) {x : P} (hx : x ∈ U) :
    HasFDerivAt (fun p => ∫ y in K, w y • k (p, y) ∂μ)
      (∫ y in K, w y • fderiv ℝ (fun z => k (z, y)) x ∂μ) x := by
  have hD := contMDiffOn_partialFDeriv hU hk
  apply hasFDerivAt_integral_compact hU hK hK.measurableSet hx
  · exact (hw.comp continuous_snd).continuousOn.smul
      (hk.continuousOn.mono (prod_mono Subset.rfl (subset_univ _)))
  · exact (hw.comp continuous_snd).continuousOn.smul
      (hD.continuousOn.mono (prod_mono Subset.rfl (subset_univ _)))
  · intro p hp y _
    have hc := ((hk (p, y) ⟨hp, mem_univ _⟩).contMDiffAt
      ((hU.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩)).comp p
      (contMDiffAt_id.prodMk contMDiffAt_const)
    exact (hc.contDiffAt.differentiableAt (by simp)).hasFDerivAt.const_smul (w y)

theorem contDiffOn_nat_weightedIntegral (n : ℕ)
    {k : P × X → ℂ} {U : Set P} {K : Set X} (hU : IsOpen U) (hK : IsCompact K)
    (hk : ContMDiffOn ((𝓘(ℝ, P)).prod (𝓘(ℝ, H))) (𝓘(ℝ, ℂ)) ∞ k (U ×ˢ univ))
    {w : X → ℂ} (hw : Continuous w) :
    ContDiffOn ℝ n (fun p => ∫ y in K, w y • k (p, y) ∂μ) U := by
  induction n generalizing k with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    have hd : DifferentiableOn ℝ (fun p => ∫ y in K, w y • k (p, y) ∂μ) U :=
      fun p hp => (hasFDerivAt_weightedIntegral hU hK hk hw hp).differentiableAt.differentiableWithinAt
    exact hd.continuousOn
  | succ n ih =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_apply hU.uniqueDiffOn]
    refine ⟨fun p hp => (hasFDerivAt_weightedIntegral hU hK hk hw hp).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    intro v
    have hD := contMDiffOn_partialFDeriv hU hk
    have hkv : ContMDiffOn ((𝓘(ℝ, P)).prod (𝓘(ℝ, H))) (𝓘(ℝ, ℂ)) ∞
        (fun p => fderiv ℝ (fun z => k (z, p.2)) p.1 v) (U ×ˢ univ) :=
      hD.clm_apply contMDiffOn_const
    apply (ih hkv).congr
    intro x hx
    rw [fderivWithin_of_isOpen hU hx, (hasFDerivAt_weightedIntegral hU hK hk hw hx).fderiv,
      ContinuousLinearMap.integral_apply]
    · rfl
    · have hcont : ContinuousOn (fun y => w y • fderiv ℝ (fun z => k (z, y)) x) K :=
        hw.continuousOn.smul ((hD.continuousOn.comp
          (continuous_const.prodMk continuous_id).continuousOn
          (fun y _ => ⟨hx, mem_univ y⟩)))
      exact hcont.integrableOn_compact hK

theorem contDiffOn_weightedIntegral
    {k : P × X → ℂ} {U : Set P} {K : Set X} (hU : IsOpen U) (hK : IsCompact K)
    (hk : ContMDiffOn ((𝓘(ℝ, P)).prod (𝓘(ℝ, H))) (𝓘(ℝ, ℂ)) ∞ k (U ×ˢ univ))
    {w : X → ℂ} (hw : Continuous w) :
    ContDiffOn ℝ ∞ (fun p => ∫ y in K, w y • k (p, y) ∂μ) U :=
  contDiffOn_infty.mpr fun n => contDiffOn_nat_weightedIntegral n hU hK hk hw

end OAI.LieTheory.Semisimple.Integration.Constructions.CharacterTriviality
