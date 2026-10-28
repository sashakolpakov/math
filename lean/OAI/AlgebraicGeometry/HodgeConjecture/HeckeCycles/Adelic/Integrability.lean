import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.FiniteOperators
import OAI.RepresentationTheory.Theta.AdelicTopology
import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier

/-! # Integrability -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Integrability.CM.Pair

/-! Integrability of real, finite, and adelic Schwartz pairings,
derived for the actual tensor-span realization. -/

open scoped Classical
open _root_.MeasureTheory
variable {I : Type*} [Fintype I]

theorem real_pair (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) : Integrable (fun x => f.val x * star (h.val x)) := by
  obtain ⟨f', hf⟩ := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.realSchwartz_mem_iff f.val).mp f.property
  obtain ⟨h', hh⟩ := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.realSchwartz_mem_iff h.val).mp h.property
  rw [hf, hh]
  apply f'.integrable.mul_bdd h'.continuous.star.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [norm_star]
    exact SchwartzMap.norm_le_seminorm ℝ h' x)

theorem finite_pair (μ : Measure (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) [μ.IsAddHaarMeasure] (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    Integrable (fun x => f.val x * star (h.val x)) μ := by
  exact ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_continuous f).mul (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_continuous h).star).integrable_of_hasCompactSupport
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_hasCompactSupport f).mul_right)

theorem tensor_pair (μ : Measure (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) [μ.IsAddHaarMeasure]
    (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) (φ η : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    Integrable (fun x => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ).val x * star ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor h η).val x)) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure μ) := by
  change Integrable _ (Measure.map RepresentationTheory.Theta.AdelicTopology.PoissonAutomorphyConstruction.adelicProductEquiv (volume.prod μ))
  rw [RepresentationTheory.Theta.AdelicTopology.PoissonAutomorphyConstruction.adelicProductEquiv.measurableEmbedding.integrable_map_iff]
  have he : (fun x : (I → ℝ) × (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) =>
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ).val (RepresentationTheory.Theta.AdelicTopology.PoissonAutomorphyConstruction.adelicProductEquiv x) * star ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor h η).val (RepresentationTheory.Theta.AdelicTopology.PoissonAutomorphyConstruction.adelicProductEquiv x))) =
      fun x => (f.val x.1 * star (h.val x.1)) * (φ.val x.2 * star (η.val x.2)) := by
    funext x
    change (f.val x.1 * φ.val x.2) * star (h.val x.1 * η.val x.2) = _
    rw [star_mul]
    ring
  change Integrable (fun x : (I → ℝ) × (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) =>
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ).val (RepresentationTheory.Theta.AdelicTopology.PoissonAutomorphyConstruction.adelicProductEquiv x) * star ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor h η).val (RepresentationTheory.Theta.AdelicTopology.PoissonAutomorphyConstruction.adelicProductEquiv x))) _
  rw [he]
  exact (real_pair f h).mul_prod (finite_pair μ φ η)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Integrability.CM.Pair

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Integrability.CM

/-! Absolute integrability of the actual adelic Schwartz tensor span,
and of its character-twisted Fourier integrands. -/

open scoped Classical
open _root_.MeasureTheory
variable {I : Type*} [Fintype I]
variable (μ : Measure (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)) [μ.IsAddHaarMeasure]

theorem tensor_integrable (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz I) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    Integrable (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ).val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure μ) := by
  obtain ⟨f', hf⟩ := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.realSchwartz_mem_iff f.val).mp f.property
  change Integrable _ (Measure.map RepresentationTheory.Theta.AdelicTopology.PoissonAutomorphyConstruction.adelicProductEquiv (volume.prod μ))
  rw [RepresentationTheory.Theta.AdelicTopology.PoissonAutomorphyConstruction.adelicProductEquiv.measurableEmbedding.integrable_map_iff]
  change Integrable (fun x : (I → ℝ) × (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) => f.val x.1 * φ.val x.2) (volume.prod μ)
  rw [hf]
  exact f'.integrable.mul_prod (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteSchwartz_integrable φ μ)

theorem integrable (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) : Integrable F.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure μ) := by
  obtain ⟨F, hF⟩ := F
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨f, φ, rfl⟩ := hF
    exact tensor_integrable μ f φ
  | zero => exact integrable_zero _ _ _
  | add F G _ _ hF hG => exact hF.add hG
  | smul c F _ hF => exact hF.smul c

theorem fourier_integrable (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) :
    Integrable (fun y => F.val y * Constructed.AdelicCharacter.CM.character (-(∑ i, x i * y i)))
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure μ) := by
  apply (CM.integrable μ F).mul_bdd
  · apply Continuous.aestronglyMeasurable
    apply Constructed.AdelicCharacter.CM.character_continuous.comp
    exact (continuous_finsetSum Finset.univ (fun i _ => continuous_const.mul (continuous_apply i))).neg
  · exact Filter.Eventually.of_forall (fun y => (Constructed.AdelicCharacter.CM.character_unitary _).le)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Integrability.CM

end

end OAI
