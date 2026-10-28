import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CohomologyComposition
import OAI.AlgebraicGeometry.Comparison.Betti.PullbackLaws
import OAI.AlgebraicGeometry.Comparison.Betti.ComponentMorphisms

/-! # Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.Naturality

noncomputable section

/-! Naturality of the actual comparison on arbitrary smooth separated finite-type schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [Smooth Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y)

theorem smoothDeRhamBettiMap_naturality (n : ℕ) :
    OpenForms.algebraicDeRhamPullback f n ≫ ReferenceCongruence.smoothDeRhamBettiMap X n =
      ReferenceCongruence.smoothDeRhamBettiMap Y n ≫ Algebraic.Sheaves.bettiPullback f n := by
  apply PullbackLaws.betti_component_hom_ext X n
  intro C
  let D := ComponentMorphisms.Components.componentTarget f C
  let fC := ComponentMorphisms.Components.componentMap f C
  let iX := Components.componentInclusion X C
  let iY := Components.componentInclusion Y D
  let : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Components.componentOver X C)) :=
    SeparatedPointTopology.finiteType_separated_complexPoints_metrizable (Components.componentOver X C)
  let : MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Components.componentOver Y D)) :=
    SeparatedPointTopology.finiteType_separated_complexPoints_metrizable (Components.componentOver Y D)
  have hf : fC ≫ iY = iX ≫ f := ComponentMorphisms.Components.componentMap_fac f C
  calc
    (OpenForms.algebraicDeRhamPullback f n ≫ ReferenceCongruence.smoothDeRhamBettiMap X n) ≫ Algebraic.Sheaves.bettiPullback iX n =
        OpenForms.algebraicDeRhamPullback f n ≫ OpenForms.algebraicDeRhamPullback iX n ≫
          Algebraic.Map.algebraicDeRhamBettiMap (Components.componentOver X C) n := by
      rw [Category.assoc, ReferenceCongruence.smoothDeRhamBettiMap_restrict_component]
    _ = OpenForms.algebraicDeRhamPullback (fC ≫ iY) n ≫
        Algebraic.Map.algebraicDeRhamBettiMap (Components.componentOver X C) n := by
      rw [← Category.assoc, Algebraic.CohomologyComposition.algebraicDeRhamPullback_comp, hf]
    _ = OpenForms.algebraicDeRhamPullback iY n ≫
        Algebraic.Map.algebraicDeRhamBettiMap (Components.componentOver Y D) n ≫ Algebraic.Sheaves.bettiPullback fC n := by
      rw [← Algebraic.CohomologyComposition.algebraicDeRhamPullback_comp, Category.assoc, Analytic.CohomologyNaturality.algebraicDeRhamBettiMap_naturality]
    _ = (ReferenceCongruence.smoothDeRhamBettiMap Y n ≫ Algebraic.Sheaves.bettiPullback iY n) ≫ Algebraic.Sheaves.bettiPullback fC n := by
      rw [ReferenceCongruence.smoothDeRhamBettiMap_restrict_component, Category.assoc]
    _ = (ReferenceCongruence.smoothDeRhamBettiMap Y n ≫ Algebraic.Sheaves.bettiPullback f n) ≫ Algebraic.Sheaves.bettiPullback iX n := by
      rw [Category.assoc, PullbackLaws.bettiPullback_comp, hf, ← PullbackLaws.bettiPullback_comp, Category.assoc]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.Naturality
