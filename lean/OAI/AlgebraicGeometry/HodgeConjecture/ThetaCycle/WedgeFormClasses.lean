import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallForms
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoverPullback
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Cm
import OAI.AlgebraicTopology.Kunneth.ProjectiveCupPurity
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Powers
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BettiConjugation

/-! # Wedge Form Classes -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.WedgeFormClasses.CM

noncomputable section

/-! Descent of finite sums of genuine theta wedges and membership of their
canonical Betti classes in the corresponding two-factor wedge spans. -/

open scoped Classical _root_.Manifold ContDiff BigOperators
open OAI.AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

theorem smooth_manifold_wedge_pullback
    {E F M Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [TopologicalSpace Y] [ChartedSpace F Y] [IsManifold 𝓘(ℝ, F) ∞ Y]
    (f : M → Y) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    {p q : ℕ} (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F Y p) (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F Y q) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback f hf (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge a b) =
      AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback f hf a) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback f hf b) := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  let : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) := inferInstanceAs (NormedAddCommGroup E)
  let : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := inferInstanceAs (NormedSpace ℝ E)
  let : NormedAddCommGroup (TangentSpace 𝓘(ℝ, F) (f x)) := inferInstanceAs (NormedAddCommGroup F)
  let : NormedSpace ℝ (TangentSpace 𝓘(ℝ, F) (f x)) := inferInstanceAs (NormedSpace ℝ F)
  exact (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge_pullback (mfderiv% f x) (a (f x)) (b (f x))).symm

def projectiveFormClassLinear (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms X.analyticModel X.analyticSpace n →ₗ[ℂ] X.complexCohomology n :=
  (X.deRhamBettiIso n).hom.hom.comp (X.deRhamClass n)

theorem closed_wedge_sum_class_mem (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (S T : Submodule ℂ (X.complexCohomology 1)) {J : Type} [Fintype J]
    (a b : J → Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms X.analyticModel X.analyticSpace 1) (c : J → ℂ)
    (ha : ∀ i, AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass X 1 (a i) ∈ S)
    (hb : ∀ i, AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass X 1 (b i) ∈ T) :
    AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass X 2 (∑ i, c i • AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge (a i) (b i)) ∈ Cm.wedgeSpan X S T := by
  change projectiveFormClassLinear X 2 _ ∈ _
  rw [map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  apply Submodule.smul_mem
  change AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass X 2 (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge (a i) (b i)) ∈ _
  rw [AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass_wedge X (a i) (b i)]
  exact Submodule.subset_span ⟨_, ha i, _, hb i, rfl⟩

theorem conjugate_closed_wedge_sum_class_mem (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (S T : Submodule ℂ (X.complexCohomology 1)) {J : Type} [Fintype J]
    (a b : J → Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms X.analyticModel X.analyticSpace 1) (c : J → ℂ)
    (ha : ∀ i, ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 X (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass X 1 (a i)) ∈ S)
    (hb : ∀ i, ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 X (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass X 1 (b i)) ∈ T) :
    AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass X 2
      (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm (∑ i, c i • AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge (a i) (b i))) ∈ Cm.wedgeSpan X S T := by
  change AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass X 2 (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedFormMap _) ∈ _
  rw [map_sum]
  simp only [map_smulₛₗ]
  change AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass X 2
    (∑ i, star (c i) • ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge (a i) (b i))) ∈ _
  simp only [ComplexMultiplication.HodgeComparison.Powers.CM.Construction.conjugateClosedForm_wedge]
  apply closed_wedge_sum_class_mem X S T _ _ (fun i => star (c i))
  · intro i
    have h : ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 X (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass X 1 (a i)) =
        AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass X 1 (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm (a i)) :=
      ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1_formClass X (a i)
    rw [← h]
    exact ha i
  · intro i
    have h : ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 X (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass X 1 (b i)) =
        AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass X 1 (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm (b i)) :=
      ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1_formClass X (b i)
    rw [← h]
    exact hb i

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d₀ d₁ : Gal(K/ℚ) → Bool}
  (L₀ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₀) (L₁ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₁)
  (N : ℕ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : B.Domain → X.analyticSpace) (hπ : B.IsBallCover N X π)

theorem closed_form_eq_sum_source_wedges {J : Type} [Fintype J]
    (a b : J → Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms X.analyticModel X.analyticSpace 1)
    (φ ψ : J → HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) (c : J → ℂ)
    (ha : ∀ i, CoverPullback.CM.ballCoverPullback K B N X π hπ 1 (a i).val = BallForms.CM.sourceBallOneForm K L₀ (φ i))
    (hb : ∀ i, CoverPullback.CM.ballCoverPullback K B N X π hπ 1 (b i).val = BallForms.CM.sourceBallOneForm K L₁ (ψ i))
    (α : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms X.analyticModel X.analyticSpace 2)
    (hα : CoverPullback.CM.ballCoverPullback K B N X π hπ 2 α.val =
      ∑ i, c i • BallForms.CM.sourceBallTwoForm K L₀ L₁ (φ i) (ψ i)) :
    α = ∑ i, c i • AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge (a i) (b i) := by
  apply Subtype.ext
  apply CoverPullback.CM.ball_cover_pullback_injective K B N X π hπ 2
  rw [hα]
  change _ = CoverPullback.CM.ballCoverPullback K B N X π hπ 2
    ((Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms X.analyticModel X.analyticSpace 2).subtype (∑ i, c i • AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge (a i) (b i)))
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change _ = Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback π _ (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge (a i).val (b i).val)
  rw [smooth_manifold_wedge_pullback]
  change _ = AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldWedge (CoverPullback.CM.ballCoverPullback K B N X π hπ 1 (a i).val)
    (CoverPullback.CM.ballCoverPullback K B N X π hπ 1 (b i).val)
  rw [ha, hb]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.WedgeFormClasses.CM
