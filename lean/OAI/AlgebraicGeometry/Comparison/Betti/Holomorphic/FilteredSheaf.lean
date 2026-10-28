import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredSections
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SheafSections

/-! # Filtered Sheaf -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredSheaf.Hodge

noncomputable section

/-! The actual holomorphic sheaf terms factor through the genuine smooth
Hodge filtration, with the original inclusion preserved exactly. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

theorem filteredFormSheafInclusion_mono (n : ℕ) (r : ℤ) :
    Mono (Filtered.SmoothComplex.Hodge.filteredFormSheafInclusion E M n r) := by
  have h (U : (Opens M)ᵒᵖ) : Mono ((Filtered.SmoothComplex.Hodge.filteredFormPresheafInclusion E M n r).app U) :=
    ConcreteCategory.mono_of_injective _ (fun _ _ h => Subtype.ext h)
  exact (sheafToPresheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)).mono_of_mono_map
    (NatTrans.mono_of_mono_app (Filtered.SmoothComplex.Hodge.filteredFormPresheafInclusion E M n r))

def holomorphicToFilteredSheaf (n : ℕ) (r : ℤ) (hr : r ≤ (n : ℤ)) :
    (SheafComplex.sheafComplex E M).X n ⟶ Filtered.SmoothComplex.Hodge.filteredFormSheaf E M n r :=
  ((sheafificationAdjunction (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)).homEquiv
    ((Presheaf.presheafComplex E M).X n) (Filtered.SmoothComplex.Hodge.filteredFormSheaf E M n r)).symm
      (FilteredSections.Hodge.holomorphicToFilteredPresheaf E M n r hr)

theorem holomorphicToFilteredSheaf_unit (n : ℕ) (r : ℤ) (hr : r ≤ (n : ℤ)) :
    toSheafify (Opens.grothendieckTopology M) ((Presheaf.presheafComplex E M).X n) ≫
      (holomorphicToFilteredSheaf E M n r hr).hom = FilteredSections.Hodge.holomorphicToFilteredPresheaf E M n r hr := by
  let adj := sheafificationAdjunction (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)
  exact (adj.homEquiv_unit _ _ (holomorphicToFilteredSheaf E M n r hr)).symm.trans
    ((adj.homEquiv _ _).apply_symm_apply _)

theorem holomorphicToFilteredSheaf_inclusion (n : ℕ) (r : ℤ) (hr : r ≤ (n : ℤ)) :
    holomorphicToFilteredSheaf E M n r hr ≫ Filtered.SmoothComplex.Hodge.filteredFormSheafInclusion E M n r =
      (SheafComplex.inclusionSheafMap E M).f n := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Opens.grothendieckTopology M) _ _ (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormSheaf E M n).property
  change (toSheafify (Opens.grothendieckTopology M)
      ((Presheaf.presheafComplex E M).X n) ≫
        (holomorphicToFilteredSheaf E M n r hr).hom ≫
          (Filtered.SmoothComplex.Hodge.filteredFormSheafInclusion E M n r).hom) = _
  erw [← Category.assoc, holomorphicToFilteredSheaf_unit]
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact (SheafSections.holomorphicSheafSectionIso_inclusion E M U.unop n a).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredSheaf.Hodge
