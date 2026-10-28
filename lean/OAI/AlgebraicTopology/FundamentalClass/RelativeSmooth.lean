import OAI.AlgebraicTopology.FundamentalClass.SmoothHomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Relative Smooth -/

namespace OAI.AlgebraicTopology.FundamentalClass.RelativeSmooth.IntegrationConstruction

noncomputable section

/-! Integration: smooth relative chains for an open submanifold, and their comparison
with the actual ordinary relative singular chains. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]

def smoothOpenMap (U : Opens M) :
    (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E U).toSSet ⟶
      (Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet :=
  Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothSingularMap E E (Subtype.val : U → M) contMDiff_subtype_val

theorem smoothOpenMap_inclusion (U : Opens M) :
    smoothOpenMap E M U ≫ Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion E M =
      Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion E U ≫ TopCat.toSSet.map (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) U) :=
  Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothSingularMap_inclusion (Subtype.val : U → M) contMDiff_subtype_val

instance smoothOpenMap_mono (U : Opens M) : Mono (smoothOpenMap E M U) := by
  have : Mono (smoothOpenMap E M U ≫ Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion E M) := by
    rw [smoothOpenMap_inclusion]
    infer_instance
  exact mono_of_mono (smoothOpenMap E M U) (Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion E M)

abbrev smoothOpenChainInclusion (U : Opens M) : SmoothHomology.IntegrationConstruction.smoothChains E U ⟶ SmoothHomology.IntegrationConstruction.smoothChains E M :=
  Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (smoothOpenMap E M U)

instance smoothOpenChainInclusion_mono (U : Opens M) : Mono (smoothOpenChainInclusion E M U) := by
  change Mono (((SSet.chainComplexFunctor (ModuleCat.{0} ℂ)).obj
    (ModuleCat.of ℂ ℂ)).map (smoothOpenMap E M U))
  dsimp [SSet.chainComplexFunctor]
  apply +allowSynthFailures Functor.map_mono

abbrev smoothRelativeChains (U : Opens M) := cokernel (smoothOpenChainInclusion E M U)

abbrev smoothRelativeProjection (U : Opens M) : SmoothHomology.IntegrationConstruction.smoothChains E M ⟶ smoothRelativeChains E M U :=
  cokernel.π (smoothOpenChainInclusion E M U)

theorem smoothOpenChainInclusion_naturality (U : Opens M) :
    smoothOpenChainInclusion E M U ≫ SmoothHomology.IntegrationConstruction.smoothChainInclusion E M =
      SmoothHomology.IntegrationConstruction.smoothChainInclusion E U ≫ AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℂ (TopCat.of M) U := by
  change SSet.chainComplexMap (smoothOpenMap E M U) (ModuleCat.of ℂ ℂ) ≫
      SSet.chainComplexMap (Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion E M) (ModuleCat.of ℂ ℂ) =
    SSet.chainComplexMap (Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion E U) (ModuleCat.of ℂ ℂ) ≫
      SSet.chainComplexMap (TopCat.toSSet.map (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) U)) (ModuleCat.of ℂ ℂ)
  change ((SSet.chainComplexFunctor (ModuleCat.{0} ℂ)).obj (ModuleCat.of ℂ ℂ)).map _ ≫
      ((SSet.chainComplexFunctor (ModuleCat.{0} ℂ)).obj (ModuleCat.of ℂ ℂ)).map _ =
    ((SSet.chainComplexFunctor (ModuleCat.{0} ℂ)).obj (ModuleCat.of ℂ ℂ)).map _ ≫
      ((SSet.chainComplexFunctor (ModuleCat.{0} ℂ)).obj (ModuleCat.of ℂ ℂ)).map _
  rw [← Functor.map_comp, ← Functor.map_comp, smoothOpenMap_inclusion]

def smoothRelativeComparison (U : Opens M) :
    smoothRelativeChains E M U ⟶ AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℂ (TopCat.of M) U :=
  cokernel.map (smoothOpenChainInclusion E M U)
    (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℂ (TopCat.of M) U)
    (SmoothHomology.IntegrationConstruction.smoothChainInclusion E U) (SmoothHomology.IntegrationConstruction.smoothChainInclusion E M)
    (smoothOpenChainInclusion_naturality E M U)

theorem smoothRelativeComparison_projection (U : Opens M) :
    smoothRelativeProjection E M U ≫ smoothRelativeComparison E M U =
      SmoothHomology.IntegrationConstruction.smoothChainInclusion E M ≫ AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℂ (TopCat.of M) U :=
  cokernel.π_desc _ _ _

def smoothRelativeSequence (U : Opens M) : ShortComplex (ChainComplex (ModuleCat.{0} ℂ) ℕ) :=
  ShortComplex.mk (smoothOpenChainInclusion E M U) (smoothRelativeProjection E M U)
    (cokernel.condition _)

theorem smoothRelativeSequence_shortExact (U : Opens M) :
    (smoothRelativeSequence E M U).ShortExact := by
  change (ShortComplex.mk (smoothOpenChainInclusion E M U)
    (cokernel.π (smoothOpenChainInclusion E M U)) _).ShortExact
  exact { exact := ShortComplex.cokernelSequence_exact (smoothOpenChainInclusion E M U) }

def smoothRelativeSequenceComparison (U : Opens M) :
    smoothRelativeSequence E M U ⟶ AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence ℂ (TopCat.of M) U where
  τ₁ := SmoothHomology.IntegrationConstruction.smoothChainInclusion E U
  τ₂ := SmoothHomology.IntegrationConstruction.smoothChainInclusion E M
  τ₃ := smoothRelativeComparison E M U
  comm₁₂ := (smoothOpenChainInclusion_naturality E M U).symm
  comm₂₃ := (smoothRelativeComparison_projection E M U).symm

theorem smoothRelativeSequence_degreewiseShortExact (U : Opens M) (n : ℕ) :
    ((smoothRelativeSequence E M U).map
      (HomologicalComplex.eval (ModuleCat.{0} ℂ) (ComplexShape.down ℕ) n)).ShortExact :=
  (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp
    (smoothRelativeSequence_shortExact E M U) n

theorem smoothRelativeProjection_surjective (U : Opens M) (n : ℕ) :
    Function.Surjective ((smoothRelativeProjection E M U).f n) := by
  let : Epi ((smoothRelativeProjection E M U).f n) :=
    (smoothRelativeSequence_degreewiseShortExact E M U n).epi_g
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

theorem smoothRelativeProjection_ker (U : Opens M) (n : ℕ) :
    LinearMap.ker ((smoothRelativeProjection E M U).f n).hom =
      LinearMap.range ((smoothOpenChainInclusion E M U).f n).hom :=
  (smoothRelativeSequence_degreewiseShortExact E M U n).exact.moduleCat_range_eq_ker.symm

variable [IsManifold 𝓘(ℝ, E) ∞ M]

theorem smoothRelativeComparison_quasiIso (U : Opens M) :
    QuasiIso (smoothRelativeComparison E M U) := by
  apply HomologicalComplex.HomologySequence.quasiIso_τ₃ (smoothRelativeSequenceComparison E M U)
    (smoothRelativeSequence_shortExact E M U)
    (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact ℂ (TopCat.of M) U)
  · exact SmoothHomology.IntegrationConstruction.smoothChainInclusion_quasiIso E U
  · exact SmoothHomology.IntegrationConstruction.smoothChainInclusion_quasiIso E M

theorem smoothRelativeHomologyComparison_injective (U : Opens M) (n : ℕ) :
    Function.Injective (HomologicalComplex.homologyMap (smoothRelativeComparison E M U) n) := by
  let := smoothRelativeComparison_quasiIso E M U
  exact (ConcreteCategory.bijective_of_isIso _).injective

end

end OAI.AlgebraicTopology.FundamentalClass.RelativeSmooth.IntegrationConstruction
