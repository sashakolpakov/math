import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StalkExactness
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.HolomorphicZeroComparison
import OAI.AlgebraicGeometry.Comparison.Betti.Module.SheafStalkQuasiIso
import OAI.AlgebraicGeometry.Comparison.Betti.SheafificationStalk
import OAI.AlgebraicGeometry.Comparison.Betti.Module.StalkExactFunctor
import OAI.Analysis.DifferentialForms.Manifold.LocalPoincare

/-! # Sheaf Quasi Iso -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SheafQuasiIso

noncomputable section

/-! The actual inclusion of the independent holomorphic de Rham sheaf complex is a quasi-isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.HomologicalComplex
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem smoothPresheafStalk_exactAt_succ (x : M) (n : ℕ) :
    (((TopCat.Presheaf.stalkFunctor (X := TopCat.of M) (ModuleCat.{0} ℂ) x).mapHomologicalComplex
      (.up ℕ)).obj (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex E M)).ExactAt (n + 1) := by
  apply AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkComplex_exactAt_succ_of_local_primitives
  intro U hx a ha
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U (n + 1) at a
  rw [Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex_d] at ha
  obtain ⟨V, hVU, hxV, b, hb⟩ := Analysis.DifferentialForms.Manifold.LocalPoincare.manifold_local_poincare U a ha ⟨x, hx⟩
  refine ⟨V, hxV, CategoryTheory.homOfLE hVU, b, ?_⟩
  rw [Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex_d]
  exact hb

omit [FiniteDimensional ℝ E] in
theorem inclusionSheafMap_quasiIsoAt_zero : QuasiIsoAt (SheafComplex.inclusionSheafMap E M) 0 := by
  apply Module.SheafStalkQuasiIso.Holomorphic.moduleSheafQuasiIsoAt_of_stalk (X := TopCat.of M) (SheafComplex.inclusionSheafMap E M) 0
  intro x
  apply SheafificationStalk.Holomorphic.sheafMap_stalk_quasiIsoAt_of_normalization (X := TopCat.of M)
    (Holomorphic.Presheaf.presheafComplex E M) (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M) (SheafComplex.inclusionSheafMap E M)
    (PresheafInclusion.inclusionPresheafCochainMap E M ≫ (SheafComplex.smoothSheafUnderlyingIso E M).inv)
    (SheafComplex.inclusionSheafMap_normalization E M) x 0
  have h := HolomorphicZeroComparison.inclusionPresheafCochainMap_quasiIsoAt_zero E M
  have hp : QuasiIsoAt
      (PresheafInclusion.inclusionPresheafCochainMap E M ≫ (SheafComplex.smoothSheafUnderlyingIso E M).inv) 0 := by
    infer_instance
  exact quasiIsoAt_map_of_preservesHomology (hφ := hp) _
    (TopCat.Presheaf.stalkFunctor (X := TopCat.of M) (ModuleCat.{0} ℂ) x) 0

theorem inclusionSheafMap_quasiIsoAt_succ (n : ℕ) :
    QuasiIsoAt (SheafComplex.inclusionSheafMap E M) (n + 1) := by
  apply Module.SheafStalkQuasiIso.Holomorphic.moduleSheafQuasiIsoAt_of_stalk (X := TopCat.of M) (SheafComplex.inclusionSheafMap E M) (n + 1)
  intro x
  apply (quasiIsoAt_iff_exactAt _ (n + 1) (StalkExactness.sheafStalk_exactAt_succ E M x n)).mpr
  let T := (TopCat.Presheaf.stalkFunctor (X := TopCat.of M) (ModuleCat.{0} ℂ) x).mapHomologicalComplex
    (.up ℕ)
  let e := T.mapIso (SheafComplex.smoothSheafUnderlyingIso E M).symm
  exact (smoothPresheafStalk_exactAt_succ E M x n).of_iso e

theorem inclusionSheafMap_quasiIso : QuasiIso (SheafComplex.inclusionSheafMap E M) := by
  apply (quasiIso_iff _).mpr
  intro n
  cases n with
  | zero => exact inclusionSheafMap_quasiIsoAt_zero E M
  | succ n => exact inclusionSheafMap_quasiIsoAt_succ E M n

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SheafQuasiIso
