import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredSheaf

/-! # Filtered Term Sections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredTermSections.Hodge

noncomputable section

/-! Exact section values and injectivity of the original holomorphic
map into each retained filtered smooth term. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

theorem holomorphicToFilteredSheaf_section (U : Opens M) (n : ℕ) (r : ℤ) (hr : r ≤ (n : ℤ))
    (a : DeRhamComplex.forms E U n) :
    (FilteredSheaf.Hodge.holomorphicToFilteredSheaf E M n r hr).hom.app (op U)
        ((SheafSections.holomorphicSheafSectionIso E M U n).hom a) =
      FilteredSections.Hodge.holomorphicToFilteredOpen E M U n r hr a := by
  have h := congrArg (fun f => f.app (op U)) (FilteredSheaf.Hodge.holomorphicToFilteredSheaf_unit E M n r hr)
  exact ConcreteCategory.congr_hom h a

omit [FiniteDimensional ℝ E] in
theorem holomorphicToFilteredOpen_injective (U : Opens M) (n : ℕ) (r : ℤ) (hr : r ≤ (n : ℤ)) :
    Function.Injective (FilteredSections.Hodge.holomorphicToFilteredOpen E M U n r hr) := by
  intro a b h
  have hv := congrArg Subtype.val h
  exact ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n).symm.injective.comp
    (HolomorphicPullback.inclusion_injective n)) hv

theorem holomorphicToFilteredSheaf_app_injective (U : Opens M) (n : ℕ) (r : ℤ)
    (hr : r ≤ (n : ℤ)) :
    Function.Injective ((FilteredSheaf.Hodge.holomorphicToFilteredSheaf E M n r hr).hom.app (op U)) := by
  intro a b h
  obtain ⟨a0, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (SheafSections.holomorphicSheafSectionIso E M U n).hom).surjective a
  obtain ⟨b0, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (SheafSections.holomorphicSheafSectionIso E M U n).hom).surjective b
  rw [holomorphicToFilteredSheaf_section, holomorphicToFilteredSheaf_section] at h
  exact congrArg _ (holomorphicToFilteredOpen_injective E M U n r hr h)

theorem holomorphicToFilteredSheaf_mono (n : ℕ) (r : ℤ) (hr : r ≤ (n : ℤ)) :
    Mono (FilteredSheaf.Hodge.holomorphicToFilteredSheaf E M n r hr) := by
  have h (U : (Opens M)ᵒᵖ) : Mono ((FilteredSheaf.Hodge.holomorphicToFilteredSheaf E M n r hr).hom.app U) :=
    ConcreteCategory.mono_of_injective _ (holomorphicToFilteredSheaf_app_injective E M U.unop n r hr)
  exact (sheafToPresheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)).mono_of_mono_map
    (NatTrans.mono_of_mono_app (FilteredSheaf.Hodge.holomorphicToFilteredSheaf E M n r hr).hom)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredTermSections.Hodge
