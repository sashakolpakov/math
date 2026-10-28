import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.TruncatedOpenCohomology
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Components

/-! # Filtered Components -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.FilteredComponents

noncomputable section

/-! The independent algebraic Hodge filtration is detected on the actual integral components, including disconnected and empty smooth schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.TruncatedOpenCohomology

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [QuasiCompact X.hom]

def componentAlgebraicTruncatedEquiv (n : ℕ) (r : ℤ) :
    FiltrationExtension.algebraicTruncatedCohomology X n r ≃ₗ[ℂ]
      (∀ C : irreducibleComponents X.left, FiltrationExtension.algebraicTruncatedCohomology (Betti.Smooth.Components.componentOver X C) n r) :=
  (DisjointDerivedHom.hypercohomologyEquiv
    (Components.componentZariskiInclusion X) (Components.componentZariskiInclusion_open X)
    (Components.componentZariskiInclusion_closed X) (Betti.Smooth.Components.componentInclusions_cover X)
    (Betti.Smooth.Components.componentInclusions_disjoint X) (FiltrationExtension.algebraicTruncationComplexInt X r) (n : ℤ)).trans
      (LinearEquiv.piCongrRight fun C =>
        TruncatedOpenCohomology.openAlgebraicTruncatedHypercohomologyEquiv (Betti.Smooth.Components.componentInclusion X C) n r)

theorem componentAlgebraicTruncatedEquiv_apply (n : ℕ) (r : ℤ)
    (a : FiltrationExtension.algebraicTruncatedCohomology X n r) (C : irreducibleComponents X.left) :
    componentAlgebraicTruncatedEquiv X n r a C =
      TruncatedOpenCohomology.openAlgebraicTruncatedHypercohomologyEquiv (Betti.Smooth.Components.componentInclusion X C) n r
        (DisjointDerivedHom.inverseImageHypercohomologyMap (Components.componentZariskiInclusion X C)
          (FiltrationExtension.algebraicTruncationComplexInt X r) (n : ℤ) a) := by
  change TruncatedOpenCohomology.openAlgebraicTruncatedHypercohomologyEquiv (Betti.Smooth.Components.componentInclusion X C) n r
    (DisjointDerivedHom.hypercohomologyEquiv (Components.componentZariskiInclusion X)
      (Components.componentZariskiInclusion_open X) (Components.componentZariskiInclusion_closed X)
      (Betti.Smooth.Components.componentInclusions_cover X) (Betti.Smooth.Components.componentInclusions_disjoint X)
      (FiltrationExtension.algebraicTruncationComplexInt X r) (n : ℤ) a C) = _
  erw [DisjointDerivedHom.hypercohomologyEquiv_apply]

theorem componentAlgebraicTruncationClass (n : ℕ) (r : ℤ)
    (a : FiltrationExtension.algebraicTruncatedCohomology X n r) (C : irreducibleComponents X.left) :
    Components.componentAlgebraicDeRhamEquiv X n (FiltrationExtension.algebraicTruncationClass X n r a) C =
      FiltrationExtension.algebraicTruncationClass (Betti.Smooth.Components.componentOver X C) n r (componentAlgebraicTruncatedEquiv X n r a C) := by
  rw [Components.componentAlgebraicDeRhamEquiv_apply, componentAlgebraicTruncatedEquiv_apply]
  exact TruncatedOpenCohomology.openAlgebraicTruncationClass_naturality (Betti.Smooth.Components.componentInclusion X C) n r a

theorem algebraicFiltration_mem_iff_components (n : ℕ) (r : ℤ) (a : Sheaves.algebraicDeRham X n) :
    a ∈ NumberTheory.PadicHodge.GeometricComparison.FilteredComplexAdapter.FormsAdapter.filtration66 X n r ↔
      ∀ C : irreducibleComponents X.left,
        Components.componentAlgebraicDeRhamEquiv X n a C ∈ NumberTheory.PadicHodge.GeometricComparison.FilteredComplexAdapter.FormsAdapter.filtration66 (Betti.Smooth.Components.componentOver X C) n r := by
  constructor
  · intro ha C
    obtain ⟨z, rfl⟩ := (FiltrationExtension.filtration66_mem_iff_truncatedClass X n r a).mp ha
    exact (FiltrationExtension.filtration66_mem_iff_truncatedClass (Betti.Smooth.Components.componentOver X C) n r _).mpr
      ⟨componentAlgebraicTruncatedEquiv X n r z C, (componentAlgebraicTruncationClass X n r z C).symm⟩
  · intro h
    have hz (C : irreducibleComponents X.left) :=
      (FiltrationExtension.filtration66_mem_iff_truncatedClass (Betti.Smooth.Components.componentOver X C) n r _).mp (h C)
    choose z hz using hz
    let a' := (componentAlgebraicTruncatedEquiv X n r).symm z
    have ha' : componentAlgebraicTruncatedEquiv X n r a' = z :=
      (componentAlgebraicTruncatedEquiv X n r).apply_symm_apply z
    refine (FiltrationExtension.filtration66_mem_iff_truncatedClass X n r a).mpr ⟨a', ?_⟩
    apply (Components.componentAlgebraicDeRhamEquiv X n).injective
    funext C
    rw [componentAlgebraicTruncationClass, ha']
    exact hz C

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.FilteredComponents
