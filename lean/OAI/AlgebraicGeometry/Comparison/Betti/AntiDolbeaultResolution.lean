import OAI.AlgebraicGeometry.Comparison.Betti.AntiDolbeaultSheafExactness
import OAI.AlgebraicGeometry.DivisorClass.Chern.ManifoldDolbeaultZeroKernel
import OAI.AlgebraicGeometry.Comparison.Betti.ResolutionExactImage

/-! # Anti Dolbeault Resolution -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AntiDolbeaultResolution

noncomputable section

/-! The original holomorphic function sheaf has its actual augmented
antiholomorphic Dolbeault resolution in every degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.HomologicalComplex
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.DivisorClass.Chern.ManifoldDolbeaultZeroKernel

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem antiManifoldDolbeaultComplex_exactAt_succ (q : ℕ) :
    (DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafComplex E M).ExactAt (q + 1) := by
  apply (HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 1 + 1) (by simp) (by simp)).mpr
  simpa only [AntiDolbeaultSheafExactness.antiManifoldDolbeaultSequence, HomologicalComplex.sc', shortComplexFunctor',
    DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafComplex, CochainComplex.of_d] using
    AntiDolbeaultSheafExactness.antiManifoldDolbeaultSequence_exact E M q

def antiManifoldDolbeaultResolution : ResolutionExactImage.Data (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) where
  complex := DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafComplex E M
  augmentation := DivisorClass.Chern.ManifoldDolbeaultZeroKernel.holomorphicToPureManifoldZeroFormSheaf
  augmentation_d := DivisorClass.Chern.ManifoldDolbeaultZeroKernel.holomorphicToPureManifoldZeroFormSheaf_d
  isKernel := by
    let S := DivisorClass.Chern.ManifoldDolbeaultZeroKernel.pureHolomorphicManifoldDolbeaultZeroSequence (E := E) (M := M)
    have : Mono S.f := DivisorClass.Chern.ManifoldDolbeaultZeroKernel.holomorphicToPureManifoldZeroFormSheaf_mono
    exact (DivisorClass.Chern.ManifoldDolbeaultZeroKernel.pureHolomorphicManifoldDolbeaultZeroSequence_exact (E := E) (M := M)).fIsKernel
  exact_succ := antiManifoldDolbeaultComplex_exactAt_succ E M

def holomorphicAntiDolbeaultAugmentation :
    (CochainComplex.single₀ (TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of M))).obj
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) ⟶ DivisorClass.Chern.PureManifoldDolbeaultSheaf.pureManifoldDolbeaultSheafComplex E M :=
  ResolutionExactImage.cochainAugmentation (antiManifoldDolbeaultResolution E M)

theorem holomorphicAntiDolbeaultAugmentation_quasiIso : QuasiIso (holomorphicAntiDolbeaultAugmentation E M) :=
  ResolutionExactImage.cochainAugmentation_quasiIso (antiManifoldDolbeaultResolution E M)

end

end OAI.AlgebraicGeometry.Comparison.Betti.AntiDolbeaultResolution
