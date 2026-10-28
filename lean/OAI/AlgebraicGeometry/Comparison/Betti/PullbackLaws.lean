import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ReferenceCongruence

/-! # Pullback Laws -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PullbackLaws

noncomputable section

/-! Composition and componentwise extensionality for the preserved Betti pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem bettiPullback_comp {X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    Algebraic.Sheaves.bettiPullback g n ≫ Algebraic.Sheaves.bettiPullback f n = Algebraic.Sheaves.bettiPullback (f ≫ g) n :=
  ((Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℂ ℂ) n ⋙ ModuleCat.uliftFunctor.{1, 0} ℂ).map_comp g.op f.op).symm

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [QuasiCompact X.hom]

theorem betti_component_hom_ext (n : ℕ) {M : ModuleCat.{1} ℂ} {a b : M ⟶ Algebraic.Sheaves.betti X n}
    (h : ∀ C : irreducibleComponents X.left,
      a ≫ Algebraic.Sheaves.bettiPullback (Betti.Smooth.Components.componentInclusion X C) n =
        b ≫ Algebraic.Sheaves.bettiPullback (Betti.Smooth.Components.componentInclusion X C) n) : a = b := by
  ext x
  apply (Betti.Smooth.ReferenceCongruence.bettiDownEquiv X n).injective
  apply (Betti.Smooth.Components.componentBettiEquiv X n).injective
  funext C
  rw [Betti.Smooth.Components.componentBettiEquiv_apply, Betti.Smooth.Components.componentBettiEquiv_apply]
  exact congrArg (Betti.Smooth.ReferenceCongruence.bettiDownEquiv (Betti.Smooth.Components.componentOver X C) n)
    (ConcreteCategory.congr_hom (h C) x)

end

end OAI.AlgebraicGeometry.Comparison.Betti.PullbackLaws
