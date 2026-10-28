import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.FilteredComponents
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.FilteredImage
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.ProjectiveFilteredComponents

/-! # Filtered Components -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.FilteredComponents

noncomputable section

/-! The exact smooth comparison map on a projective presentation is the original comparison on each of its independently defined Hodge components. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

local instance : Smooth P.toOver.hom := P.smooth
local instance : IsProper P.toOver.hom := P.projective.isProper
attribute [local instance] Betti.Smooth.ReferenceCongruence.componentMetrizable

local instance (C : irreducibleComponents P.carrier) :
    IsIntegral (Betti.Smooth.Components.componentOver P.toOver C).left :=
  Betti.Smooth.Components.componentOverIntegral P.toOver C
local instance (C : irreducibleComponents P.carrier) :
    Smooth (Betti.Smooth.Components.componentOver P.toOver C).hom :=
  Betti.Smooth.Components.componentOverSmooth P.toOver C
local instance (C : irreducibleComponents P.carrier) :
    MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Betti.Smooth.Components.componentOver P.toOver C)) :=
  Betti.Smooth.ReferenceCongruence.componentMetrizable P.toOver C

theorem projective_componentBettiEquiv_normalization (n : ℕ) (b : P.complexCohomology n)
    (C : irreducibleComponents P.carrier) :
    P.componentBettiEquiv (ModuleCat.of ℂ ℂ) n b C = Betti.Smooth.Components.componentBettiEquiv P.toOver n b C := by
  erw [P.componentBettiEquiv_apply]

theorem projective_smoothComparison_component (n : ℕ) (a : Algebraic.Sheaves.algebraicDeRham P.toOver n)
    (C : irreducibleComponents P.carrier) :
    P.componentBettiEquiv (ModuleCat.of ℂ ℂ) n (Target.smoothDeRhamBettiLinearMap P.toOver n a) C =
      Betti.Smooth.ReferenceCongruence.bettiDownEquiv (Betti.Smooth.Components.componentOver P.toOver C) n
        (Algebraic.Map.algebraicDeRhamBettiMap (Betti.Smooth.Components.componentOver P.toOver C) n
          (Algebraic.Components.componentAlgebraicDeRhamEquiv P.toOver n a C)) := by
  erw [projective_componentBettiEquiv_normalization, Algebraic.Components.componentAlgebraicDeRhamEquiv_apply]
  exact Betti.Smooth.ReferenceCongruence.smoothDeRhamBettiMap_component P.toOver n a C

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.FilteredComponents
