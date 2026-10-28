import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanSpace
import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylSynthesis
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Weyl Synthesis Analysis -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.WeylSynthesisAnalysis.Construction

noncomputable section

/-! Integrable Weyl superpositions are continuous. Compact smooth Bruhat
tests separate continuous functions, allowing exact reconstruction without
assuming that a synthesized function is already Schwartz. -/

open _root_.MeasureTheory Filter
open scoped ComplexConjugate ContDiff

theorem weylSynthesis_continuous
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}
    (ψ : AddChar k ℂ) (hc : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
    (ν : Measure (Local.FunctionsMetaplectic.Construction.PhaseSpace k N)) (a : Local.FunctionsMetaplectic.Construction.PhaseSpace k N → ℂ) (ha : Continuous a) (hai : Integrable a ν)
    (u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) : Continuous (UnitarySplitting.WeylSynthesisAdd.Construction.weylSynthesis ψ ν a u.val) := by
  obtain ⟨C, -, hb⟩ := UnitarySplitting.TestSpaceAnalysis.Construction.schwartzBruhat_norm_bound u.property
  have huc := TestSpace.LocalAnalysis.schwartzBruhat_continuous u.property
  have hkernel : Continuous (fun z : Local.FunctionsMetaplectic.Construction.Position k N × Local.FunctionsMetaplectic.Construction.PhaseSpace k N =>
      a z.2 * Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ z.2 u.val z.1) := by
    unfold Local.FunctionsMetaplectic.Construction.heisenbergFunction
    fun_prop
  rw [continuous_iff_continuousAt]
  intro x
  apply tendsto_integral_filter_of_dominated_convergence (fun v => ‖a v‖ * C)
  · exact Eventually.of_forall fun y =>
      (hkernel.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Eventually.of_forall fun y => Eventually.of_forall fun v => by
      simp only [Local.FunctionsMetaplectic.Construction.heisenbergFunction, norm_mul, hu, one_mul]
      exact mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)
  · exact hai.norm.mul_const C
  · exact Eventually.of_forall fun v =>
      (hkernel.comp (continuous_id.prodMk continuous_const)).continuousAt.tendsto

theorem continuous_eq_of_compact_smooth_pairings
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (f g : V → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hpair : ∀ b : V → ℝ, ContDiff ℝ ∞ b → HasCompactSupport b →
      (∫ x, b x • f x ∂μ) = ∫ x, b x • g x ∂μ) : f = g := by
  have he : f =ᵐ[μ] g :=
    ae_eq_of_integral_contDiff_smul_eq hf.locallyIntegrable hg.locallyIntegrable hpair
  exact Measure.eq_of_ae_eq he hf hg

def compactSmoothRealBruhat
    {k : Type} [NormedField k] [NormedAlgebra ℝ k] [FiniteDimensional ℝ k] {N : ℕ}
    (b : Local.FunctionsMetaplectic.Construction.Position k N → ℝ) (hbc : ContDiff ℝ ∞ b) (hbs : HasCompactSupport b) : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N := by
  let φ : SchwartzMap (Local.FunctionsMetaplectic.Construction.Position k N) ℂ :=
    (hbs.toSchwartzMap hbc).postcompCLM Complex.ofRealCLM
  exact ⟨φ, ArchimedeanCharacters.LocalAnalysis.schwartzBruhat_archimedean_iff.mpr ⟨φ, rfl⟩⟩

theorem compactSmoothRealBruhat_apply
    {k : Type} [NormedField k] [NormedAlgebra ℝ k] [FiniteDimensional ℝ k] {N : ℕ}
    (b : Local.FunctionsMetaplectic.Construction.Position k N → ℝ) (hbc : ContDiff ℝ ∞ b) (hbs : HasCompactSupport b) (x : Local.FunctionsMetaplectic.Construction.Position k N) :
    (compactSmoothRealBruhat b hbc hbs).val x = (b x : ℂ) := rfl

theorem continuous_eq_of_bruhat_pairings
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [NormedAlgebra ℝ k] [FiniteDimensional ℝ k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {N : ℕ}
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k N)) [μ.IsAddHaarMeasure]
    (f g : Local.FunctionsMetaplectic.Construction.Position k N → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hpair : ∀ u : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N,
      (∫ x, f x * conj (u.val x) ∂μ) = ∫ x, g x * conj (u.val x) ∂μ) : f = g := by
  apply continuous_eq_of_compact_smooth_pairings μ f g hf hg
  intro b hbc hbs
  have hp := hpair (compactSmoothRealBruhat b hbc hbs)
  simp only [compactSmoothRealBruhat_apply, Complex.conj_ofReal] at hp
  simpa only [Complex.real_smul, mul_comm] using hp

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.WeylSynthesisAnalysis.Construction
