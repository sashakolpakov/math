import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.FilteredComponents
import OAI.AlgebraicGeometry.Comparison.Betti.Filtered.LinearComponents
import OAI.AlgebraicGeometry.Comparison.Betti.Target

/-! # Filtered Image -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.FilteredImage

noncomputable section

/-! The exact image of the algebraic Hodge filtration under the original smooth comparison is detected by its actual component maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
attribute [local instance] ReferenceCongruence.componentMetrizable

def smoothComponentFiltrationImage (n : ℕ) (r : ℤ)
    (b : Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) X n) : Prop :=
      ∀ C : irreducibleComponents X.left,
        ∃ a : Algebraic.Sheaves.algebraicDeRham (Components.componentOver X C) n,
          a ∈ NumberTheory.PadicHodge.GeometricComparison.FilteredComplexAdapter.FormsAdapter.filtration66 (Components.componentOver X C) n r ∧
          ReferenceCongruence.bettiDownEquiv (Components.componentOver X C) n (Algebraic.Map.algebraicDeRhamBettiMap (Components.componentOver X C) n a) =
            Components.componentBettiEquiv X n b C

theorem smoothComparison_filtration_image_mem_iff (n : ℕ) (r : ℤ)
    (b : Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) X n) :
    b ∈ (Target.algebraicHodgeFiltration X n r).map (Target.smoothDeRhamBettiLinearMap X n) ↔
      smoothComponentFiltrationImage X n r b := by
  unfold smoothComponentFiltrationImage
  let g (C : irreducibleComponents X.left) :
      Algebraic.Sheaves.algebraicDeRham (Components.componentOver X C) n →ₗ[ℂ]
        Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) (Components.componentOver X C) n :=
    (ReferenceCongruence.bettiDownEquiv (Components.componentOver X C) n).toLinearMap.comp
      (Algebraic.Map.algebraicDeRhamBettiMap (Components.componentOver X C) n).hom
  have hf (a : Algebraic.Sheaves.algebraicDeRham X n) (C : irreducibleComponents X.left) :
      Components.componentBettiEquiv X n (Target.smoothDeRhamBettiLinearMap X n a) C =
        g C (Algebraic.Components.componentAlgebraicDeRhamEquiv X n a C) := by
    erw [Algebraic.Components.componentAlgebraicDeRhamEquiv_apply]
    exact ReferenceCongruence.smoothDeRhamBettiMap_component X n a C
  exact Filtered.LinearComponents.mem_map_iff_components
    (Algebraic.Components.componentAlgebraicDeRhamEquiv X n) (Components.componentBettiEquiv X n)
    (Target.smoothDeRhamBettiLinearMap X n) g (Target.algebraicHodgeFiltration X n r)
    (fun C => NumberTheory.PadicHodge.GeometricComparison.FilteredComplexAdapter.FormsAdapter.filtration66 (Components.componentOver X C) n r)
    (Algebraic.FilteredComponents.algebraicFiltration_mem_iff_components X n r) hf b

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.FilteredImage
