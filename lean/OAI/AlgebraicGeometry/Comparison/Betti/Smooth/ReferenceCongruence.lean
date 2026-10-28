import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Map
import OAI.AlgebraicGeometry.Comparison.Betti.SeparatedPointTopology
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.Components

/-! # Reference Congruence -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence

noncomputable section

section

/-!
# The comparison map under the natural smooth variety hypotheses

The actual integral-component inclusions pull back algebraic
hypercohomology. Their constructed comparisons assemble using the proved
Betti restriction equivalence. No integrality or analytic metrizability
assumption is imposed on the original scheme, including the empty scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

local instance componentMetrizable (C : irreducibleComponents X.left) :
    MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (Components.componentOver X C)) :=
  SeparatedPointTopology.finiteType_separated_complexPoints_metrizable (Components.componentOver X C)

/-- The canonical universe equivalence for the preserved Betti target. -/
def bettiDownEquiv (Y : Over Foundations.Scheme.ProjectiveSpace.complexBase) (n : ℕ) :
    Algebraic.Sheaves.betti Y n ≃ₗ[ℂ] Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) Y n := ULift.moduleEquiv

def componentComparison (n : ℕ) (C : irreducibleComponents X.left) :
    Algebraic.Sheaves.algebraicDeRham X n →ₗ[ℂ]
      Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) (Components.componentOver X C) n :=
  (bettiDownEquiv (Components.componentOver X C) n).toLinearMap.comp
    ((Algebraic.Map.algebraicDeRhamBettiMap (Components.componentOver X C) n).hom.comp
      (OpenForms.algebraicDeRhamPullback (Components.componentInclusion X C) n).hom)

/-- The constructed map for every smooth separated finite-type complex scheme. -/
def smoothDeRhamBettiMap (n : ℕ) : Algebraic.Sheaves.algebraicDeRham X n ⟶ Algebraic.Sheaves.betti X n :=
  ModuleCat.ofHom ((bettiDownEquiv X n).symm.toLinearMap.comp
    ((Components.componentBettiEquiv X n).symm.toLinearMap.comp
      (LinearMap.pi (componentComparison X n))))

theorem smoothDeRhamBettiMap_component (n : ℕ) (a : Algebraic.Sheaves.algebraicDeRham X n)
    (C : irreducibleComponents X.left) :
    Components.componentBettiEquiv X n
        (bettiDownEquiv X n (smoothDeRhamBettiMap X n a)) C = componentComparison X n C a := by
  change Components.componentBettiEquiv X n
      ((bettiDownEquiv X n) ((bettiDownEquiv X n).symm
        ((Components.componentBettiEquiv X n).symm (fun D => componentComparison X n D a)))) C = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The assembled map restricts to exactly the previously constructed comparison on each component. -/
theorem smoothDeRhamBettiMap_restrict_component (n : ℕ) (C : irreducibleComponents X.left) :
    smoothDeRhamBettiMap X n ≫ Algebraic.Sheaves.bettiPullback (Components.componentInclusion X C) n =
      OpenForms.algebraicDeRhamPullback (Components.componentInclusion X C) n ≫
        Algebraic.Map.algebraicDeRhamBettiMap (Components.componentOver X C) n := by
  ext a
  apply (bettiDownEquiv (Components.componentOver X C) n).injective
  have h := smoothDeRhamBettiMap_component X n a C
  rw [Components.componentBettiEquiv_apply] at h
  exact h

end

/-! Equality of the underlying scheme preserves the original comparison, independently of proofs of the structural hypotheses. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [IsIntegral Y.left] [Smooth Y.hom]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]

theorem originalBettiComparison_congr (h : X = Y) (n : ℕ)
    (a : Algebraic.Sheaves.algebraicDeRham X n) (b : Algebraic.Sheaves.algebraicDeRham Y n) (hab : HEq a b) :
    HEq (bettiDownEquiv X n (Algebraic.Map.algebraicDeRhamBettiMap X n a))
      (bettiDownEquiv Y n (Algebraic.Map.algebraicDeRhamBettiMap Y n b)) := by
  subst Y
  cases hab
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence
