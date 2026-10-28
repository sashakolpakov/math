import OAI.AlgebraicGeometry.Comparison.Betti.Filtered.PresheafComplex
import OAI.AlgebraicGeometry.Comparison.Betti.Filtered.LocalPoincare
import OAI.AlgebraicTopology.Cohomology.Singular.StalkExactnessAt

/-! # Stalk Exactness -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Filtered.StalkExactness.Hodge

noncomputable section

/-! Actual filtered smooth presheaf and sheaf stalks are exact in each
positive degree strictly above the integer filtration index. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem filteredPresheafStalk_exactAt_succ (r : ℤ) (x : M) (n : ℕ) (hr : r ≤ (n : ℤ)) :
    (((TopCat.Presheaf.stalkFunctor (X := TopCat.of M) (ModuleCat.{0} ℂ) x).mapHomologicalComplex
      (.up ℕ)).obj (PresheafComplex.Hodge.filteredSmoothPresheafComplex E M r)).ExactAt (n + 1) := by
  apply AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkComplex_exactAt_succ_of_local_primitives
  intro U hx a ha
  change Open.FiltrationDescent.Hodge.openFormFiltration (E := E) U (n + 1) r at a
  rw [PresheafComplex.Hodge.filteredSmoothPresheafComplex_d] at ha
  have hclosed : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a.val = 0 := congrArg Subtype.val ha
  obtain ⟨V, hxV, hVU, b, hbf, hb⟩ := LocalPoincare.Hodge.filtered_local_poincare U n r hr a.val a.property hclosed ⟨x, hx⟩
  refine ⟨V, hxV, homOfLE hVU, ⟨b, hbf⟩, ?_⟩
  rw [PresheafComplex.Hodge.filteredSmoothPresheafComplex_d]
  exact Subtype.ext hb

variable [FiniteDimensional ℝ E]

theorem filteredSheafStalk_exactAt_succ (r : ℤ) (x : M) (n : ℕ) (hr : r ≤ (n : ℤ)) :
    (((TopCat.Sheaf.forget (ModuleCat.{0} ℂ) (TopCat.of M) ⋙
      TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℂ) x).mapHomologicalComplex (.up ℕ)).obj
        (SmoothComplex.Hodge.filteredSmoothSheafComplex E M r)).ExactAt (n + 1) := by
  let T := (TopCat.Presheaf.stalkFunctor (X := TopCat.of M) (ModuleCat.{0} ℂ) x).mapHomologicalComplex (.up ℕ)
  let e := T.mapIso (PresheafComplex.Hodge.filteredSmoothSheafUnderlyingIso E M r).symm
  exact (filteredPresheafStalk_exactAt_succ E M r x n hr).of_iso e

end

end OAI.AlgebraicGeometry.Comparison.Betti.Filtered.StalkExactness.Hodge
