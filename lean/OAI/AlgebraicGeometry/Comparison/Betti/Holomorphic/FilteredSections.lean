import OAI.AlgebraicGeometry.Comparison.Betti.Filtered.SmoothComplex
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.LocalDescent

/-! # Filtered Sections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredSections.Hodge

noncomputable section

/-! The original holomorphic realization lands in the actual smooth
Hodge filtration in every retained degree. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

theorem ambientHolomorphicInclusion_filtered (U : Opens M) (n : ℕ) (r : ℤ)
    (hr : r ≤ (n : ℤ)) (a : DeRhamComplex.forms E U n) :
    LocalDescent.ambientHolomorphicInclusion U n a ∈ Open.FiltrationDescent.Hodge.openFormFiltration U n r := by
  change Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n
      ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n).symm (DeRhamComplex.inclusion E U n a)) ∈
    ManifoldFormFiltration.Hodge.manifoldFormFiltration E U n r
  rw [LinearEquiv.apply_symm_apply]
  apply Submodule.mem_iSup_of_mem (⟨(n, 0), Nat.add_zero n⟩ : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n)
  apply Submodule.mem_iSup_of_mem hr
  exact a.val.property

def holomorphicToFilteredOpen (U : Opens M) (n : ℕ) (r : ℤ) (hr : r ≤ (n : ℤ)) :
    DeRhamComplex.forms E U n →ₗ[ℂ] Open.FiltrationDescent.Hodge.openFormFiltration (E := E) U n r where
  toFun a := ⟨LocalDescent.ambientHolomorphicInclusion U n a,
    ambientHolomorphicInclusion_filtered E M U n r hr a⟩
  map_add' a b := Subtype.ext ((LocalDescent.ambientHolomorphicInclusion U n).map_add a b)
  map_smul' c a := Subtype.ext ((LocalDescent.ambientHolomorphicInclusion U n).map_smul c a)

theorem holomorphicToFilteredOpen_d (U : Opens M) (n : ℕ) (r : ℤ)
    (hr : r ≤ (n : ℤ)) (hr' : r ≤ ((n + 1 : ℕ) : ℤ)) (a : DeRhamComplex.forms E U n) :
    Filtered.SmoothComplex.Hodge.filteredOpenDifferential E M U n r (holomorphicToFilteredOpen E M U n r hr a) =
      holomorphicToFilteredOpen E M U (n + 1) r hr' (DeRhamComplex.differential E U n a) := by
  apply Subtype.ext
  apply (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (n + 1)).injective
  change Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (n + 1)
      (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d
        ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n).symm (DeRhamComplex.inclusion E U n a))) =
    Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (n + 1)
      ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (n + 1)).symm
        (DeRhamComplex.inclusion E U (n + 1) (DeRhamComplex.differential E U n a)))
  rw [← Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_d, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, DeRhamComplex.inclusion_differential]

def holomorphicToFilteredPresheaf (n : ℕ) (r : ℤ) (hr : r ≤ (n : ℤ)) :
    (Presheaf.presheafComplex E M).X n ⟶ Filtered.SmoothComplex.Hodge.filteredFormPresheaf E M n r where
  app U := ModuleCat.ofHom (holomorphicToFilteredOpen E M U.unop n r hr)
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact Subtype.ext (LocalDescent.ambientHolomorphicInclusion_restrict
      (leOfHom f.unop) n a).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredSections.Hodge
