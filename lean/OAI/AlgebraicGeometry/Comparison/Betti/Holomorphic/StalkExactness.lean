import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.LocalPoincare
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SheafComplex
import OAI.AlgebraicGeometry.Comparison.Betti.SheafificationStalkComplex
import OAI.AlgebraicTopology.Cohomology.Singular.StalkExactnessAt

/-! # Stalk Exactness -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StalkExactness

noncomputable section

/-! Positive-degree exactness of the actual holomorphic presheaf and sheaf stalks. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem presheafStalk_exactAt_succ (x : M) (n : ℕ) :
    (((TopCat.Presheaf.stalkFunctor (X := TopCat.of M) (ModuleCat.{0} ℂ) x).mapHomologicalComplex (.up ℕ)).obj
      (Holomorphic.Presheaf.presheafComplex E M)).ExactAt (n + 1) := by
  apply AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkComplex_exactAt_succ_of_local_primitives
  intro U hx a ha
  change DeRhamComplex.forms E U (n + 1) at a
  change (DeRhamComplex.complex E U).d (n + 1) (n + 2) a = 0 at ha
  rw [DeRhamComplex.complex_d] at ha
  obtain ⟨V, hVU, hxV, b, hb⟩ := LocalPoincare.local_primitive_on U a ha ⟨x, hx⟩
  refine ⟨V, hxV, homOfLE hVU, b, ?_⟩
  change (DeRhamComplex.complex E V).d n (n + 1) b = _
  rw [DeRhamComplex.complex_d]
  exact hb

theorem sheafStalk_exactAt_succ (x : M) (n : ℕ) :
    (((TopCat.Sheaf.forget (ModuleCat.{0} ℂ) (TopCat.of M) ⋙
      TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℂ) x).mapHomologicalComplex (.up ℕ)).obj
        (SheafComplex.sheafComplex E M)).ExactAt (n + 1) := by
  let e := asIso (SheafificationStalkComplex.Holomorphic.sheafificationStalkUnit (X := TopCat.of M) (Holomorphic.Presheaf.presheafComplex E M) x)
  exact (presheafStalk_exactAt_succ E M x n).of_iso e

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StalkExactness
