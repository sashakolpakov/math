import OAI.RepresentationTheory.Theta.Geometric.AbelianHodgeOne
import OAI.RepresentationTheory.Theta.Geometric.AbelianHolomorphicAlgebraization
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Naturality
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicPrimitive

/-! # Albanese Closed Form Lift -/

namespace OAI.RepresentationTheory.Theta.Geometric.AlbaneseClosedFormLift

noncomputable section

section

/-! An actual algebraic map inducing an H¹ isomorphism lifts each
holomorphic Betti class to an algebraic one-form on its abelian target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

theorem projectiveComplexH1_bijective_of_rational
    (X Y : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (f : X.toOver ⟶ Y.toOver)
    (hf : Function.Bijective (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 f)) :
    Function.Bijective (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f) := by
  let e : Y.rationalCohomology 1 ≃ₗ[ℚ] X.rationalCohomology 1 :=
    LinearEquiv.ofBijective (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 f).hom hf
  let cX := AlgebraicGeometry.HodgeConjecture.CMExtraction.Mem.bettiComplexification X.presentation 1
  let cY := AlgebraicGeometry.HodgeConjecture.CMExtraction.Mem.bettiComplexification Y.presentation 1
  let b := cY.symm.trans ((e.baseChange ℚ ℂ _ _).trans cX)
  have hb : (b : Y.complexCohomology 1 → X.complexCohomology 1) =
      AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f := by
    funext a
    have h := AlgebraicGeometry.HodgeConjecture.CMExtraction.Naturality.complexification_pullback f 1 (cY.symm a)
    change b a = AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f (cY (cY.symm a)) at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h
  exact hb ▸ b.bijective

variable (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : X.toOver ⟶ A.toOver)
    (hf : Function.Bijective (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 f))

def abelianH1PullbackEquiv : A.variety.complexCohomology 1 ≃ₗ[ℂ] X.complexCohomology 1 :=
  LinearEquiv.ofBijective (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f).hom
    (projectiveComplexH1_bijective_of_rational X A.variety f hf)

def abelianPureBettiInverse : X.pureBettiSubspace 1 0 →ₗ[ℂ] A.variety.pureBettiSubspace 1 0 where
  toFun a := ⟨(abelianH1PullbackEquiv X A f hf).symm a.val,
    AbelianHodgeOne.abelianPullback_holomorphic_reflection X A f
      (projectiveComplexH1_bijective_of_rational X A.variety f hf).1 _ (by
        change abelianH1PullbackEquiv X A f hf ((abelianH1PullbackEquiv X A f hf).symm a.val) ∈ _
        rw [LinearEquiv.apply_symm_apply]
        exact a.property)⟩
  map_add' a b := Subtype.ext ((abelianH1PullbackEquiv X A f hf).symm.map_add a.val b.val)
  map_smul' c a := Subtype.ext ((abelianH1PullbackEquiv X A f hf).symm.map_smul c a.val)

def algebraicLiftAlongAbelianMap : X.pureBettiSubspace 1 0 →ₗ[ℂ] AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms A.toOver :=
  (AbelianHolomorphicAlgebraization.abelianPureBettiAlgebraicLift A).comp (abelianPureBettiInverse X A f hf)

theorem algebraicLiftAlongAbelianMap_class (a : X.pureBettiSubspace 1 0) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerBettiClass X (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback f (algebraicLiftAlongAbelianMap X A f hf a)) = a.val := by
  rw [AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerBettiClass_pullback]
  change AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.kaehlerBettiClass A.variety (AbelianHolomorphicAlgebraization.abelianPureBettiAlgebraicLift A (abelianPureBettiInverse X A f hf a))) = _
  rw [AbelianHolomorphicAlgebraization.abelianPureBettiAlgebraicLift_class]
  exact (abelianH1PullbackEquiv X A f hf).apply_symm_apply a.val

end

/-! The algebraic lift along an H¹-isomorphism to an abelian variety
pulls back to the actual closed holomorphic form, not just its Betti class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

variable (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

def closedHolomorphicBettiLinear :
    AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0 →ₗ[ℂ]
      X.pureBettiSubspace 1 0 where
  toFun a := ⟨(X.deRhamBettiIso 1).hom (X.deRhamClass 1 a.val), by
    apply (X.mem_pureBettiSubspace_iff 1 0 _).mpr
    exact ⟨a.val, (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _).mp a.property, rfl⟩⟩
  map_add' a b := by
    apply Subtype.ext
    change (X.deRhamBettiIso 1).hom (X.deRhamClass 1 (a.val + b.val)) =
      (X.deRhamBettiIso 1).hom (X.deRhamClass 1 a.val) +
        (X.deRhamBettiIso 1).hom (X.deRhamClass 1 b.val)
    rw [map_add, map_add]
  map_smul' c a := by
    apply Subtype.ext
    change (X.deRhamBettiIso 1).hom (X.deRhamClass 1 (c • a.val)) =
      c • (X.deRhamBettiIso 1).hom (X.deRhamClass 1 a.val)
    rw [map_smul, map_smul]

variable (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ A.toOver)
    (hf : Function.Bijective (AlgebraicGeometry.Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 f))

def algebraicLiftClosedHolomorphic :
    AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0 →ₗ[ℂ] AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms A.toOver :=
  (algebraicLiftAlongAbelianMap X A f hf).comp (closedHolomorphicBettiLinear X)

theorem algebraicLiftClosedHolomorphic_pullback
    (a : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.closedKaehlerRealization X (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback f (algebraicLiftClosedHolomorphic X A f hf a)) = a.val := by
  let b := AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerClasses.Intrinsic.closedKaehlerRealization X (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback f (algebraicLiftClosedHolomorphic X A f hf a))
  have hb : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree X.analyticModel X.analyticSpace 1 0 b.val.val := by
    let : IsIntegral X.toOver.left := X.property
    let : Smooth X.toOver.hom := X.presentation.smooth
    let : X.toOver.left.IsSeparated := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicForms.integralProjective_separated X
    exact AlgebraicGeometry.HodgeConjecture.CMExtraction.OpenPurity.Kaehler.globalSmoothForm_pure X.toOver _
  have hc : X.deRhamClass 1 b = X.deRhamClass 1 a.val := by
    apply (X.deRhamBettiIso 1).toLinearEquiv.injective
    exact algebraicLiftAlongAbelianMap_class X A f hf (closedHolomorphicBettiLinear X a)
  have he : (⟨b, hb⟩ : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0) = a :=
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.holomorphic_formClass_injective hc
  exact congrArg Subtype.val he

end

end OAI.RepresentationTheory.Theta.Geometric.AlbaneseClosedFormLift
