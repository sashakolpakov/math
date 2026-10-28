import OAI.RepresentationTheory.Theta.Geometric.BettiConjugationInvolution
import OAI.RepresentationTheory.Theta.Geometric.AbelianHodgeOne
import OAI.RepresentationTheory.Theta.Geometric.AbelianHolomorphicAlgebraization
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses

/-! # One Form Betti Faithfulness -/

namespace OAI.RepresentationTheory.Theta.Geometric.OneFormBettiFaithfulness

noncomputable section

/-! Pullback on actual algebraic one-forms determines the full complex
Betti H1 pullback from an abelian variety, using both conjugate Hodge pieces. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic

theorem abelian_complexBetti_eq_of_forms (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f g : X.toOver ⟶ A.toOver)
    (h : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback f = AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback g) :
    (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f).hom = (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 g).hom := by
  have hp (x : A.variety.complexCohomology 1) (hx : x ∈ A.variety.pureBettiSubspace 1 0) :
      AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f x = AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 g x := by
    let a : A.variety.pureBettiSubspace 1 0 := ⟨x, hx⟩
    have he : AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerBettiClass A.variety (AbelianHolomorphicAlgebraization.abelianPureBettiAlgebraicLift A a) = x :=
      AbelianHolomorphicAlgebraization.abelianPureBettiAlgebraicLift_class A a
    rw [← he]
    rw [← AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerBettiClass_pullback, ← AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerBettiClass_pullback, h]
  have ha (x : A.variety.complexCohomology 1) (hx : x ∈ A.variety.pureBettiSubspace 0 1) :
      AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f x = AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 g x := by
    apply (BettiConjugationInvolution.conjugateBetti_involutive X).injective
    rw [BettiConjugationInvolution.conjugateBetti_pullback, BettiConjugationInvolution.conjugateBetti_pullback]
    exact hp _ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1_antiholomorphic A.variety x hx)
  ext x
  have hx : x ∈ A.variety.pureBettiSubspace 1 0 ⊔ A.variety.pureBettiSubspace 0 1 := by
    rw [AbelianHodgeOne.abelianPureH1_sup_top]
    trivial
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, map_add, hp y hy, ha z hz]

theorem abelian_rationalBetti_eq_of_forms (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f g : X.toOver ⟶ A.toOver)
    (h : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback f = AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback g) :
    (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 f).hom = (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 g).hom := by
  have hc := abelian_complexBetti_eq_of_forms X A f g h
  ext x
  apply AlgebraicGeometry.Betti.Scheme.schemeBettiRationalInclusion_injective X.toOver 1
  have hf := ConcreteCategory.congr_hom (AlgebraicGeometry.Betti.Scheme.schemeBettiRationalInclusion_naturality f 1) x
  have hg := ConcreteCategory.congr_hom (AlgebraicGeometry.Betti.Scheme.schemeBettiRationalInclusion_naturality g 1) x
  exact hf.trans ((LinearMap.congr_fun hc (AlgebraicGeometry.Betti.Scheme.schemeBettiRationalInclusion A.toOver 1 x)).trans hg.symm)

end

end OAI.RepresentationTheory.Theta.Geometric.OneFormBettiFaithfulness
