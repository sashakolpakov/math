import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ThetaClass
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodForms
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicPrimitive

/-! # Nonzero Class -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NonzeroClass

noncomputable section

/-! Nonvanishing passes from the actual period covector to the native
integration-defined Betti class. Exact holomorphic one-forms vanish on
the compact projective component. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem thetaBettiComponent_eq_zero_iff (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (j : Fin D.pel.componentCount) (φ : D.sphericalInputs) :
    ClosedForms.thetaBettiComponent D hg Θ j φ = 0 ↔ IntrinsicForms.thetaSmoothComponent D hg Θ j φ = 0 := by
  constructor
  · intro hz
    let V := D.componentVariety hg j
    have hc : V.deRhamClass 1 (ClosedForms.thetaClosedComponent D hg Θ j φ) = 0 := by
      apply (V.deRhamBettiIso 1).toLinearEquiv.injective
      exact hz.trans (map_zero (V.deRhamBettiIso 1).toLinearEquiv).symm
    have hf := ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.holomorphic_oneForm_eq_zero_of_class_eq_zero
      (ClosedForms.thetaClosedComponent D hg Θ j φ) (IntrinsicForms.thetaSmoothComponent_pure D hg Θ j φ) hc
    exact congrArg Subtype.val hf
  · intro hz
    have hf : ClosedForms.thetaClosedComponent D hg Θ j φ = 0 := Subtype.ext hz
    change ((D.componentVariety hg j).deRhamBettiIso 1).hom
      ((D.componentVariety hg j).deRhamClass 1 (ClosedForms.thetaClosedComponent D hg Θ j φ)) = 0
    rw [hf, map_zero, map_zero]

theorem nativeThetaClass_ne_zero_of_period_value (hg : D.pel.HasIntegralModelGeometry)
    (Θ : D.sphericalInputs →ₗ[ℂ] D.pel.OneFormsA)
    (j : Fin D.pel.componentCount) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex j)
    (cover : D.domain → X.analyticSpace) (hcover : D.IsPeriodUniformization X cover)
    (hΘ : D.IsCanonicalThetaLift hg j (D.totalPeriodMap j X component cover) Θ)
    (φ : D.sphericalInputs) (x : D.domain) (u : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates)
    (hvalue : D.thetaUniversal φ.val x.val u ≠ 0) :
    ThetaClass.nativeThetaClass D hg Θ φ ≠ 0 := by
  intro hz
  have hcomp : ClosedForms.thetaComplexifiedComponent D hg Θ j φ = 0 := by
    rw [← ThetaClass.nativeThetaClass_component, hz, map_zero]
    rfl
  have hbetti : ClosedForms.thetaBettiComponent D hg Θ j φ = 0 := by
    have h := congrArg (Mem.bettiComplexification (D.componentVariety hg j).presentation 1) hcomp
    change (Mem.bettiComplexification (D.componentVariety hg j).presentation 1)
      ((Mem.bettiComplexification (D.componentVariety hg j).presentation 1).symm
        (ClosedForms.thetaBettiComponent D hg Θ j φ)) = _ at h
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using h
  have hsmooth := (thetaBettiComponent_eq_zero_iff D hg Θ j φ).mp hbetti
  have hperiod : PeriodForms.thetaOnPeriodVariety D hg Θ j X component φ = 0 := by
    rw [PeriodForms.thetaOnPeriodVariety_native, hsmooth, map_zero]
  let hc := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hcover.2.2.1
  have hcovector :
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback cover (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hc)
        (PeriodForms.thetaOnPeriodVariety D hg Θ j X component φ)).val.inChart
          (chartAt RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates x) x.val (fun _ => u) = D.thetaUniversal φ.val x.val u :=
    PeriodForms.thetaOnPeriodVariety_covector D hg Θ j X component cover hcover hΘ φ x u
  have hzero : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback cover (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hc)
      (PeriodForms.thetaOnPeriodVariety D hg Θ j X component φ) = 0 := by
    rw [hperiod]
    exact map_zero _
  rw [hzero] at hcovector
  exact hvalue hcovector.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NonzeroClass
