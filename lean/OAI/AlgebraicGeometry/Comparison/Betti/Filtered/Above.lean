import OAI.AlgebraicGeometry.Comparison.Betti.Filtered.StalkExactness
import OAI.AlgebraicGeometry.Comparison.Betti.Brutal
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredComplex
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StalkExactness
import OAI.AlgebraicGeometry.Comparison.Betti.Module.SheafStalkQuasiIso
import OAI.AlgebraicGeometry.Comparison.Betti.Module.StalkExactFunctor

/-! # Above -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Filtered.Above.Hodge

noncomputable section

/-! The actual truncated holomorphic-to-filtered-smooth comparison is
a quasi-isomorphism in every positive degree above the cutoff. -/

open _root_.CategoryTheory _root_.TopologicalSpace _root_.HomologicalComplex
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem holomorphicFilteredSheafMap_quasiIsoAt_above (r : ℤ) (n : ℕ) (hr : r ≤ (n : ℤ)) :
    QuasiIsoAt (Holomorphic.FilteredComplex.Hodge.holomorphicFilteredSheafMap E M r) (n + 1) := by
  apply Module.SheafStalkQuasiIso.Holomorphic.moduleSheafQuasiIsoAt_of_stalk (X := TopCat.of M)
    (Holomorphic.FilteredComplex.Hodge.holomorphicFilteredSheafMap E M r) (n + 1)
  intro x
  let F : Holomorphic.SheafComplex.sheafCategory M ⥤ ModuleCat.{0} ℂ :=
    sheafToPresheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ) ⋙
    TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℂ) x
  have hF : F.PreservesZeroMorphisms := by
    constructor
    intro A B
    change (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℂ) x).map (0 : A.obj ⟶ B.obj) = 0
    exact Functor.map_zero _ _ _
  have hcut := Brutal.Complex.brutal_inclusion_map_quasiIsoAt_succ
    (Holomorphic.SheafComplex.sheafComplex E M) F r n hr
  have hsource := (quasiIsoAt_iff_exactAt'
    ((F.mapHomologicalComplex (.up ℕ)).map (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (Holomorphic.SheafComplex.sheafComplex E M) r))
    (n + 1) (Holomorphic.StalkExactness.sheafStalk_exactAt_succ E M x n)).mp hcut
  apply (quasiIsoAt_iff_exactAt _ (n + 1) hsource).mpr
  exact StalkExactness.Hodge.filteredSheafStalk_exactAt_succ E M r x n hr

end

end OAI.AlgebraicGeometry.Comparison.Betti.Filtered.Above.Hodge
