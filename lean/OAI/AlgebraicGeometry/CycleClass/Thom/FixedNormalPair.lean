import OAI.AlgebraicGeometry.CycleClass.Thom.Degree
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalCoordinatesDifferentiable

/-! # Fixed Normal Pair -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.FixedNormalPair.Constructions

noncomputable section

/-! A genuine holomorphic embedded immersion supplies analytic normal pairs in the specified codimension. -/

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalCoordinatesDifferentiable
open scoped _root_.Manifold ContDiff

theorem exists_analytic_normalPair {E F M N : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ω N]
    (f : M → N) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω f)
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) f x))
    (he : Topology.IsEmbedding f) (p : ℕ) (hp : Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension E F = p) (x : M) :
    ∃ P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) f x,
      P.ambientChart.MDifferentiable 𝓘(ℂ, F) 𝓘(ℂ, E × (Fin p → ℂ)) ∧
      ContMDiffOn 𝓘(ℂ, F) 𝓘(ℂ, E × (Fin p → ℂ)) ω P.ambientChart P.ambientChart.source ∧
      ContMDiffOn 𝓘(ℂ, E × (Fin p → ℂ)) 𝓘(ℂ, F) ω P.ambientChart.symm P.ambientChart.target := by
  have h : Manifold.IsImmersionOfComplement (Fin p → ℂ) 𝓘(ℂ, E) 𝓘(ℂ, F) ω f := by
    have h := Geometric.ComplexNormalAtlas.Cycles.complexImmersion_standardComplement f hf hi
    rwa [hp] at h
  exact ⟨ComplexPoints.Analytic.NormalPairRecenter.normalPairOfImmersion (h x) he,
    ComplexPoints.Analytic.NormalCoordinatesDifferentiable.normalPairOfImmersion_ambientChart_mdifferentiable (h x) he (by simp),
    ComplexPoints.Analytic.NormalCoordinatesDifferentiable.contMDiffOn_immersionNormalCoordinates (h x), ComplexPoints.Analytic.NormalCoordinatesDifferentiable.contMDiffOn_immersionNormalCoordinates_symm (h x)⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.FixedNormalPair.Constructions
