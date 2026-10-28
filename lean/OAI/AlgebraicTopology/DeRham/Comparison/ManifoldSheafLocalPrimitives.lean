import OAI.Analysis.DifferentialForms.Manifold.SheafDeRham
import OAI.Analysis.DifferentialForms.Manifold.ComplexSheafHomology
import OAI.AlgebraicTopology.Cohomology.Singular.StalkExactnessAt

/-! # Manifold Sheaf Local Primitives -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ManifoldSheafLocalPrimitives

noncomputable section

/-!
# Local primitives and exactness of the manifold de Rham sheaves

This proves the categorical passage from genuine local primitives of smooth
tangent-covector fields to exactness of their complex of sheaves. The model
space has the ordinary universe of finite-dimensional vector spaces; the
underlying manifold can be in any universe. The local-primitive hypothesis
is explicit and will be supplied by the analytic local Poincare theorem.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

universe u

local instance manifoldSheafPreadditive (X : TopCat.{u}) :
    Preadditive (TopCat.Sheaf (ModuleCat.{u} ℂ) X) :=
  Analysis.DifferentialForms.Manifold.ManifoldSheaf.complexModuleSheafPreadditiveAny X

local instance manifoldSheafCategoryWithHomology (X : TopCat.{u}) :
    CategoryWithHomology (TopCat.Sheaf (ModuleCat.{u} ℂ) X) := by
  convert (CategoryTheory.categoryWithHomology_of_abelian
    (C := TopCat.Sheaf (ModuleCat.{u} ℂ) X)) using 1
  exact Subsingleton.elim _ _

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The already constructed manifold complex has homology with its existing
pointwise zero morphisms. -/
instance manifoldDeRhamSheafComplex_hasHomology (n : ℕ) :
    (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M).HasHomology n := by
  infer_instance

/-- Two consecutive exterior derivatives of actual smooth manifold sheaves. -/
def manifoldDeRhamSheafStep (n : ℕ) :
    ShortComplex (TopCat.Sheaf (ModuleCat.{u} ℂ) (TopCat.of M)) :=
  ShortComplex.mk (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheafD E M n) (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheafD E M (n + 1))
    (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheafD_squared E M n)

/-- A local primitive condition involving only genuine open-domain manifold
forms, actual exterior differentiation and restriction. -/
def HasLocalSmoothManifoldPrimitives (n : ℕ) : Prop :=
  ∀ (U : Opens M) (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U (n + 1)),
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d form = 0 → ∀ x : U,
      ∃ (V : Opens M) (hVU : V ≤ U), (x : M) ∈ V ∧
        ∃ primitive : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E V n,
          Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d primitive = Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hVU form

/-- Actual local smooth primitives give categorical exactness of the manifold
form sheaves, by the local criterion for their actual stalks. -/
theorem manifoldDeRhamSheafStep_exact_of_local_primitives (n : ℕ)
    (hlocal : HasLocalSmoothManifoldPrimitives E M n) :
    (manifoldDeRhamSheafStep E M n).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
    (manifoldDeRhamSheafStep E M n)).2
  intro x
  change (((manifoldDeRhamSheafStep E M n).map
    (TopCat.Sheaf.forget (ModuleCat.{u} ℂ) (TopCat.of M))).map
      (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} ℂ) x)).Exact
  apply Cohomology.Singular.StalkExactnessAt.stalk_exact_of_locally_exact
  intro U hx form hclosed
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U (n + 1) at form
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d form = 0 at hclosed
  obtain ⟨V, hVU, hxV, primitive, hprimitive⟩ := hlocal U form hclosed ⟨x, hx⟩
  exact ⟨V, hxV, homOfLE hVU, primitive, hprimitive⟩

/-- The local primitive condition implies exactness in degree `n+1` of the
already constructed manifold de Rham sheaf complex. -/
theorem manifoldDeRhamSheafComplex_exactAt_of_local_primitives (n : ℕ)
    (hlocal : HasLocalSmoothManifoldPrimitives E M n) :
    (Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M).ExactAt (n + 1) := by
  rw [(Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M).exactAt_iff' n (n + 1) (n + 2)
    (by simp) (by simp)]
  simpa only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex_X, Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex_d,
    manifoldDeRhamSheafStep] using
      manifoldDeRhamSheafStep_exact_of_local_primitives E M n hlocal

/-- The corresponding positive homology sheaf is zero. -/
theorem manifoldDeRhamSheafComplex_isZero_homology_of_local_primitives (n : ℕ)
    (hlocal : HasLocalSmoothManifoldPrimitives E M n) :
    IsZero ((Analysis.DifferentialForms.Manifold.SheafDeRham.manifoldDeRhamSheafComplex E M).homology (n + 1)) :=
  (manifoldDeRhamSheafComplex_exactAt_of_local_primitives E M n hlocal).isZero_homology

end

end OAI.AlgebraicTopology.DeRham.Comparison.ManifoldSheafLocalPrimitives
