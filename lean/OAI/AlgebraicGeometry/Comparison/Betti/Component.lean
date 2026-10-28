import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Components
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence

/-! # Component -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Component

noncomputable section

section

/-! The actual smooth comparison is the componentwise map under the proved decompositions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

attribute [local instance] Betti.Smooth.ReferenceCongruence.componentMetrizable

def componentLiftedBettiEquiv (n : ℕ) :
    Algebraic.Sheaves.betti X n ≃ₗ[ℂ] (∀ C : irreducibleComponents X.left,
      Algebraic.Sheaves.betti (Betti.Smooth.Components.componentOver X C) n) :=
  (Betti.Smooth.ReferenceCongruence.bettiDownEquiv X n).trans ((Betti.Smooth.Components.componentBettiEquiv X n).trans
    (LinearEquiv.piCongrRight fun C => (Betti.Smooth.ReferenceCongruence.bettiDownEquiv (Betti.Smooth.Components.componentOver X C) n).symm))

omit [IsSeparated X.hom] in
theorem componentLiftedBettiEquiv_apply (n : ℕ) (a : Algebraic.Sheaves.betti X n)
    (C : irreducibleComponents X.left) :
    componentLiftedBettiEquiv X n a C = Algebraic.Sheaves.bettiPullback (Betti.Smooth.Components.componentInclusion X C) n a := by
  apply (Betti.Smooth.ReferenceCongruence.bettiDownEquiv (Betti.Smooth.Components.componentOver X C) n).injective
  change (Betti.Smooth.ReferenceCongruence.bettiDownEquiv (Betti.Smooth.Components.componentOver X C) n)
    ((Betti.Smooth.ReferenceCongruence.bettiDownEquiv (Betti.Smooth.Components.componentOver X C) n).symm
      (Betti.Smooth.Components.componentBettiEquiv X n (Betti.Smooth.ReferenceCongruence.bettiDownEquiv X n a) C)) = _
  rw [LinearEquiv.apply_symm_apply, Betti.Smooth.Components.componentBettiEquiv_apply]
  rfl

def componentwiseComparison (n : ℕ) :
    (∀ C : irreducibleComponents X.left, Algebraic.Sheaves.algebraicDeRham (Betti.Smooth.Components.componentOver X C) n) →ₗ[ℂ]
      (∀ C : irreducibleComponents X.left, Algebraic.Sheaves.betti (Betti.Smooth.Components.componentOver X C) n) :=
  LinearMap.pi fun C => (Algebraic.Map.algebraicDeRhamBettiMap (Betti.Smooth.Components.componentOver X C) n).hom.comp
    (LinearMap.proj C)

theorem smoothDeRhamBettiMap_componentwise (n : ℕ) (a : Algebraic.Sheaves.algebraicDeRham X n) :
    componentLiftedBettiEquiv X n (Betti.Smooth.ReferenceCongruence.smoothDeRhamBettiMap X n a) =
      componentwiseComparison X n (Algebraic.Components.componentAlgebraicDeRhamEquiv X n a) := by
  funext C
  rw [componentLiftedBettiEquiv_apply]
  change Algebraic.Sheaves.bettiPullback (Betti.Smooth.Components.componentInclusion X C) n (Betti.Smooth.ReferenceCongruence.smoothDeRhamBettiMap X n a) =
    Algebraic.Map.algebraicDeRhamBettiMap (Betti.Smooth.Components.componentOver X C) n
      (Algebraic.Components.componentAlgebraicDeRhamEquiv X n a C)
  erw [Algebraic.Components.componentAlgebraicDeRhamEquiv_apply]
  exact ConcreteCategory.congr_hom (Betti.Smooth.ReferenceCongruence.smoothDeRhamBettiMap_restrict_component X n C) a

theorem smoothDeRhamBettiMap_factorization (n : ℕ) :
    (Betti.Smooth.ReferenceCongruence.smoothDeRhamBettiMap X n).hom =
      (componentLiftedBettiEquiv X n).symm.toLinearMap.comp
        ((componentwiseComparison X n).comp
          (Algebraic.Components.componentAlgebraicDeRhamEquiv X n).toLinearMap) := by
  apply LinearMap.ext
  intro a
  apply (componentLiftedBettiEquiv X n).injective
  change componentLiftedBettiEquiv X n (Betti.Smooth.ReferenceCongruence.smoothDeRhamBettiMap X n a) =
    componentLiftedBettiEquiv X n ((componentLiftedBettiEquiv X n).symm _)
  rw [LinearEquiv.apply_symm_apply]
  exact smoothDeRhamBettiMap_componentwise X n a

end

/-! Isomorphisms of the original integral-component comparisons give an isomorphism of the original smooth comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

attribute [local instance] Betti.Smooth.ReferenceCongruence.componentMetrizable

theorem smoothDeRhamBettiMap_isIso_of_components (n : ℕ)
    (h : ∀ C : irreducibleComponents X.left,
      IsIso (Algebraic.Map.algebraicDeRhamBettiMap (Betti.Smooth.Components.componentOver X C) n)) :
    IsIso (Betti.Smooth.ReferenceCongruence.smoothDeRhamBettiMap X n) := by
  have hb (C : irreducibleComponents X.left) :
      Function.Bijective (Algebraic.Map.algebraicDeRhamBettiMap (Betti.Smooth.Components.componentOver X C) n) := by
    have := h C
    exact ConcreteCategory.bijective_of_isIso _
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y hxy
    apply (Algebraic.Components.componentAlgebraicDeRhamEquiv X n).injective
    funext C
    apply (hb C).injective
    have hx := congrFun (smoothDeRhamBettiMap_componentwise X n x) C
    have hy := congrFun (smoothDeRhamBettiMap_componentwise X n y) C
    exact hx.symm.trans
      ((congrArg (fun a => componentLiftedBettiEquiv X n a C) hxy).trans hy)
  · intro y
    choose a ha using fun C => (hb C).surjective (componentLiftedBettiEquiv X n y C)
    refine ⟨(Algebraic.Components.componentAlgebraicDeRhamEquiv X n).symm a, ?_⟩
    apply (componentLiftedBettiEquiv X n).injective
    rw [smoothDeRhamBettiMap_componentwise]
    rw [(Algebraic.Components.componentAlgebraicDeRhamEquiv X n).apply_symm_apply]
    funext C
    exact ha C

end

end OAI.AlgebraicGeometry.Comparison.Betti.Component
