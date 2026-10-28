import OAI.AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
import OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient

/-! # Smooth Homology -/

namespace OAI.AlgebraicTopology.FundamentalClass.SmoothHomology.IntegrationConstruction

noncomputable section

/-! Integration: passage from the checked smooth cochain comparison to genuine
smooth homology representatives, using field-valued universal coefficients. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

theorem homology_bijective_of_cohomology_bijective
    {F : Type} [Field F] {K L : SSet.{0}} (f : K ⟶ L) (n : ℕ)
    (hf : Function.Bijective
      (HomologicalComplex.homologyMap (Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of F F) f) n)) :
    Function.Bijective (Cohomology.Singular.EvaluationNaturality.simplicialHomologyPushforward (R := F) f n) := by
  let uK := Cohomology.Singular.UniversalCoefficient.simplicialUniversalCoefficientEquiv (F := F) K n
  let uL := Cohomology.Singular.UniversalCoefficient.simplicialUniversalCoefficientEquiv (F := F) L n
  let h := HomologicalComplex.homologyMap (Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of F F) f) n
  have he : (Cohomology.Singular.EvaluationNaturality.simplicialHomologyPushforward (R := F) f n).hom.dualMap =
      uK.toLinearMap.comp (h.hom.comp uL.symm.toLinearMap) := by
    apply LinearMap.ext
    intro φ
    obtain ⟨c, rfl⟩ := uL.surjective φ
    apply LinearMap.ext
    intro z
    change uL c (Cohomology.Singular.EvaluationNaturality.simplicialHomologyPushforward (R := F) f n z) =
      uK (h (uL.symm (uL c))) z
    rw [uL.symm_apply_apply]
    exact (Cohomology.Singular.EvaluationNaturality.simplicialHomologyEvaluation_naturality (ModuleCat.of F F) f n c z).symm
  apply LinearMap.dualMap_bijective_iff.mp
  rw [he]
  exact uK.bijective.comp (hf.comp uL.symm.bijective)

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

abbrev smoothChains :=
  Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℂ) (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet

abbrev smoothChainInclusion : smoothChains E M ⟶ Cohomology.Singular.Evaluation.singularScalarChains (R := ℂ) (TopCat.of M) :=
  Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion E M)

theorem smoothHomologyInclusion_bijective (n : ℕ) :
    Function.Bijective (HomologicalComplex.homologyMap (smoothChainInclusion E M) n) := by
  apply homology_bijective_of_cohomology_bijective
  exact (Cohomology.Singular.GlobalSmoothComparison.manifoldSmoothCohomologyIso E M n).toLinearEquiv.bijective

theorem smoothChainInclusion_quasiIso : QuasiIso (smoothChainInclusion E M) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact (ConcreteCategory.isIso_iff_bijective _).mpr (smoothHomologyInclusion_bijective E M n)

/-- Every complex singular class has an actual finite smooth-cycle representative. -/
theorem exists_smooth_cycle_representative (n : ℕ)
    (z : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℂ) (TopCat.of M)).homology n) :
    ∃ c : Cohomology.Singular.ChainRepresentatives.chainCycles (smoothChains E M) n,
      HomologicalComplex.homologyMap (smoothChainInclusion E M) n
        (Cohomology.Singular.ChainRepresentatives.chainClass (smoothChains E M) n c) = z := by
  obtain ⟨a, ha⟩ := (smoothHomologyInclusion_bijective E M n).surjective z
  obtain ⟨c, hc⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (smoothChains E M) n a
  exact ⟨c, hc ▸ ha⟩

end

end OAI.AlgebraicTopology.FundamentalClass.SmoothHomology.IntegrationConstruction
