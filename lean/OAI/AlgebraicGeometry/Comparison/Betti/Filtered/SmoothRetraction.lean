import OAI.AlgebraicGeometry.Comparison.Betti.Open.ChartEvaluation
import OAI.AlgebraicGeometry.Comparison.Betti.Filtered.SmoothComplex

/-! # Smooth Retraction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Filtered.SmoothRetraction.Hodge

noncomputable section

/-! Each actual filtered smooth form sheaf is a direct summand of the
original smooth form sheaf, by the finite sum of its allowed type projectors. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff BigOperators

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

def allowedTypeProjection (U : Opens M) (n : ℕ) (r : ℤ) :
    Module.End ℂ (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :=
  ∑ i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n, if r ≤ (i.val.1 : ℤ) then Open.FiltrationDescent.Hodge.openTypeProjection U n i else 0

theorem allowedTypeProjection_mem (U : Opens M) (n : ℕ) (r : ℤ)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) : allowedTypeProjection E M U n r a ∈ Open.FiltrationDescent.Hodge.openFormFiltration U n r := by
  unfold allowedTypeProjection
  rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : r ≤ (i.val.1 : ℤ)
  · rw [ite_eq_left hi]
    exact Open.ChartEvaluation.Hodge.openPureFormsInDegree_mem_filtration U n i r hi _ (Open.ChartEvaluation.Hodge.openTypeProjection_pure U n i a)
  · rw [ite_eq_right hi]
    exact Submodule.zero_mem _

theorem allowedTypeProjection_identity (U : Opens M) (n : ℕ) (r : ℤ)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) (ha : a ∈ Open.FiltrationDescent.Hodge.openFormFiltration U n r) :
    allowedTypeProjection E M U n r a = a := by
  rw [allowedTypeProjection, LinearMap.sum_apply]
  conv_rhs => rw [← Open.ChartEvaluation.Hodge.sum_openTypeProjection U n a]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : r ≤ (i.val.1 : ℤ)
  · rw [ite_eq_left hi]
  · rw [ite_eq_right hi]
    exact ((Open.FiltrationDescent.Hodge.mem_openFormFiltration_iff_projections U n r a).mp ha i (lt_of_not_ge hi)).symm

theorem allowedTypeProjection_restrict {U V : Opens M} (h : V ≤ U) (n : ℕ) (r : ℤ)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h (allowedTypeProjection E M U n r a) =
      allowedTypeProjection E M V n r (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h a) := by
  simp only [allowedTypeProjection, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : r ≤ (i.val.1 : ℤ)
  · simp only [ite_eq_left hi]
    exact Open.FiltrationDescent.Hodge.openTypeProjection_restrict h n i a
  · simp only [ite_eq_right hi, LinearMap.zero_apply, map_zero]

def openFiltrationProjection (U : Opens M) (n : ℕ) (r : ℤ) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n →ₗ[ℂ] Open.FiltrationDescent.Hodge.openFormFiltration (E := E) U n r :=
  (allowedTypeProjection E M U n r).codRestrict _ (allowedTypeProjection_mem E M U n r)

def filteredFormPresheafRetraction (n : ℕ) (r : ℤ) :
    Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf E M n ⟶ SmoothComplex.Hodge.filteredFormPresheaf E M n r where
  app U := ModuleCat.ofHom (openFiltrationProjection E M U.unop n r)
  naturality {U V} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact Subtype.ext (allowedTypeProjection_restrict E M (leOfHom h.unop) n r a).symm

def filteredFormSheafRetraction (n : ℕ) (r : ℤ) :
    Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M n ⟶ SmoothComplex.Hodge.filteredFormSheaf E M n r :=
  ObjectProperty.homMk (filteredFormPresheafRetraction E M n r)

theorem filteredFormSheafInclusion_retraction (n : ℕ) (r : ℤ) :
    SmoothComplex.Hodge.filteredFormSheafInclusion E M n r ≫ filteredFormSheafRetraction E M n r = 𝟙 _ := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact Subtype.ext (allowedTypeProjection_identity E M U.unop n r a.val a.property)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Filtered.SmoothRetraction.Hodge
