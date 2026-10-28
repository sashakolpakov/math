import OAI.AlgebraicGeometry.AbelianVariety.AveragePeriods
import OAI.AlgebraicGeometry.AbelianVariety.TranslationCohomology
import OAI.AlgebraicGeometry.AbelianVariety.InvariantCohomology
import OAI.AlgebraicTopology.DeRham.Comparison.Manifold
import OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass

/-! # Cycle Periods -/

namespace OAI.AlgebraicGeometry.AbelianVariety.CyclePeriods.Constructions.ExteriorCohomology

noncomputable section

/-!
# Invariant forms compute compact connected commutative Lie-group cohomology

Haar averaging preserves periods on every genuine smooth singular cycle.
Universal coefficient duality and the actual integration comparison show that
averaging preserves de Rham classes, proving the invariant-form comparison.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient
open scoped _root_.Manifold ContDiff _root_.Topology Simplicial
open Set Filter _root_.MeasureTheory

theorem span_simplexChains (K : SSet.{0}) (n : ℕ) :
    Submodule.span ℂ (Set.range (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℂ) K (n := n))) = ⊤ := by
  let S := Submodule.span ℂ (Set.range (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℂ) K (n := n)))
  have h : S.mkQ = 0 := by
    apply AlgebraicTopology.Cohomology.Singular.ChainDual.chainFunctional_ext K (ModuleCat.of ℂ ((AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℂ) K).X n ⧸ S))
    intro σ
    change Submodule.Quotient.mk (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain K σ) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨σ, rfl⟩
  have hk := congrArg LinearMap.ker h
  simpa only [Submodule.ker_mkQ, LinearMap.ker_zero] using hk

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Group G] [TopologicalSpace G] [ChartedSpace E G] [LieGroup 𝓘(ℝ, E) ∞ G] {n : ℕ}

def smoothChainPeriod (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) :
    (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℂ) (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E G).toSSet).X n →ₗ[ℂ] ℂ :=
  AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E G).toSSet (ModuleCat.of ℂ ℂ) n
    (AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E G n form)

theorem smoothChainPeriod_simplex (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (σ : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E G).toSSet _⦋n⦌) :
    smoothChainPeriod form (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain _ σ) = AlgebraicTopology.DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration σ form := by
  rw [smoothChainPeriod, AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex, AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain_evaluation]

variable [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
  (μ : Measure G) [IsFiniteMeasure μ] [Measure.IsMulRightInvariant μ]

theorem smoothChainPeriod_averageForms (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (z : (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℂ) (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E G).toSSet).X n) :
    Integrable (fun g => smoothChainPeriod
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (fun h : G => g * h)
        (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)) form) z) μ ∧
      smoothChainPeriod (Averaging.Constructions.ExteriorCohomology.averageForms μ form) z =
        ∫ g, smoothChainPeriod
          (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (fun h : G => g * h)
            (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)) form) z ∂μ := by
  have hz : z ∈ Submodule.span ℂ
      (Set.range (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℂ) (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E G).toSSet (n := n))) := by
    rw [span_simplexChains]
    trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨σ, rfl⟩ := hx
      simp only [smoothChainPeriod_simplex]
      exact ⟨AveragePeriods.Constructions.ExteriorCohomology.smoothSimplexIntegration_translated_integrable μ form σ,
        AveragePeriods.Constructions.ExteriorCohomology.smoothSimplexIntegration_averageForms μ form σ⟩
  | zero => simp
  | add x y hx hy hix hiy =>
      simp only [map_add]
      exact ⟨hix.1.add hiy.1, by rw [hix.2, hiy.2, integral_add hix.1 hiy.1]⟩
  | smul a x hx hix =>
      simp only [map_smul]
      exact ⟨hix.1.smul a, by rw [hix.2, integral_smul]⟩

omit [MeasurableSpace G] [BorelSpace G] [CompactSpace G] in
theorem smoothCyclePeriod_translation [ConnectedSpace G]
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E G n)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℂ)
      (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E G).toSSet) n) (g : G) :
    smoothChainPeriod (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (fun h : G => g * h)
      (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)) form.val) z.val =
        smoothChainPeriod form.val z.val := by
  have he := TranslationCohomology.Constructions.Exterior.leftTranslation_integrationClass (E := E) g n form
  let K := (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E G).toSSet
  have hp := congrArg (fun a : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) G).homology n =>
    AlgebraicTopology.Cohomology.Singular.Evaluation.simplicialHomologyEvaluation K (ModuleCat.of ℂ ℂ) n a
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℂ) K) n z)) he
  rw [AlgebraicTopology.Cohomology.Singular.Evaluation.simplicialHomologyEvaluation_class_class, AlgebraicTopology.Cohomology.Singular.Evaluation.simplicialHomologyEvaluation_class_class] at hp
  exact hp

def averageClosedForm (n : ℕ) : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E G n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E G n :=
  ((Averaging.Constructions.ExteriorCohomology.averageForms μ).comp (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E G n).subtype).codRestrict
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E G n) (fun form => by
      change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Averaging.Constructions.ExteriorCohomology.averageForms μ form.val) = 0
      rw [AveragingDerivative.Constructions.ExteriorCohomology.d_averageForms, form.property, map_zero])

theorem averageClosedForm_integrationClass [ConnectedSpace G] [IsProbabilityMeasure μ]
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E G n) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) G) n
      (AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E G n (averageClosedForm μ n form)) =
      AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) G) n
        (AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E G n form) := by
  let K := (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E G).toSSet
  apply AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.simplicialHomologyEvaluation_injective K n
  apply LinearMap.ext
  intro h
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℂ) K) n h
  rw [AlgebraicTopology.Cohomology.Singular.Evaluation.simplicialHomologyEvaluation_class_class, AlgebraicTopology.Cohomology.Singular.Evaluation.simplicialHomologyEvaluation_class_class]
  change smoothChainPeriod (Averaging.Constructions.ExteriorCohomology.averageForms μ form.val) z.val = smoothChainPeriod form.val z.val
  rw [(smoothChainPeriod_averageForms μ form.val z.val).2]
  simp only [smoothCyclePeriod_translation form z, integral_const, probReal_univ, one_smul]

variable [FiniteDimensional ℝ E] [T2Space G] [ConnectedSpace G]

theorem averageClosedForm_deRhamClass [IsProbabilityMeasure μ]
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E G n) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E G n (averageClosedForm μ n form) =
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E G n form := by
  apply (AlgebraicTopology.DeRham.Comparison.Manifold.manifoldDeRhamSmoothCohomologyIso E G n).toLinearEquiv.injective
  change AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap E G n
      (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E G n (averageClosedForm μ n form)) =
    AlgebraicTopology.DeRham.Comparison.SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap E G n (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E G n form)
  rw [AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCohomologyMap_formClass,
    AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCohomologyMap_formClass]
  exact averageClosedForm_integrationClass μ form

variable [IsMulCommutative G]

theorem invariantDeRham_surjective_compact (n : ℕ) :
    Function.Surjective (InvariantCohomology.Constructions.Exterior.invariantDeRham (E := E) (G := G) n) := by
  intro a
  obtain ⟨form, rfl⟩ := Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamFormClass_surjective E G n a
  let μ₀ := Averaging.Constructions.ExteriorCohomology.compactGroupHaar (E := E) (G := G)
  refine ⟨⟨Averaging.Constructions.ExteriorCohomology.averageForms μ₀ form.val, Averaging.Constructions.ExteriorCohomology.averageForms_mem μ₀ form.val⟩, ?_⟩
  change Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E G n (averageClosedForm μ₀ n form) =
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E G n form
  exact averageClosedForm_deRhamClass μ₀ form

def invariantDeRhamEquiv (n : ℕ) :
    InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) n ≃ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology E G n :=
  LinearEquiv.ofBijective (InvariantCohomology.Constructions.Exterior.invariantDeRham n)
    ⟨InvariantCohomology.Constructions.Exterior.invariantDeRham_injective_compact n, invariantDeRham_surjective_compact n⟩

end

end OAI.AlgebraicGeometry.AbelianVariety.CyclePeriods.Constructions.ExteriorCohomology
