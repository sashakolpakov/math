import OAI.RepresentationTheory.Theta.Geometric.Cleared.BranchTraceModels
import OAI.RepresentationTheory.Theta.Geometric.Active.FormClearing
import OAI.RepresentationTheory.Theta.Geometric.IteratedSchemePullback

/-! # Branch Trace Models -/

namespace OAI.RepresentationTheory.Theta.Geometric.Active.BranchTraceModels

noncomputable section

/-! The active rational Hecke operator is the raw differentiated sum
over the original branches with their actual corrected targets. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj _root_.Manifold ContDiff

namespace ActiveHeckeThetaData

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : TateComparison.Action D.pel)
    (hA : A.IsRealization D.pel hg hgood hIsogenyQuotient)
    (j : Fin D.pel.componentCount) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex j)
    (cover : D.domain → X.analyticSpace) (hcover : D.IsPeriodUniformization X cover)
    (w : Intrinsic.Hecke.ActiveWeight)

local notation "Branches" => D.ClearedBranch (D.totalPeriodMap j X component cover) w
local notation "Correspondence" => D.pel.complexCorrespondence (OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished w)

include hA in
theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.exists_activeBranchTrace_models [Fintype Branches] :
    let hc := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hcover.2.2.1
    ∃ (Y : Branches → AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
      (target : ∀ b, (Y b).toOver ⟶ D.pel.complexSpace)
      (l : ∀ b, D.domain → (Y b).analyticSpace)
      (hl : ∀ b, ContMDiff 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, (Y b).analyticModel) ∞ (l b)),
      (∀ b x, l b x ≫ target b = D.clearedBranchTarget A.shift b x) ∧
      ∀ form : D.pel.OneFormsA,
        Projective.FormOnDomain.projectiveFormOnDomain D.domain X cover hc
          (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (component.hom ≫ D.componentComplexInclusion j)
            (D.pel.albanesePullback hg
              (D.heckeRationalForms hg A (A.basis (Intrinsic.Hecke.activeType D.pel.reference.distinguished w)) form))) =
          ∑ b : Branches, Projective.FormOnDomain.projectiveFormOnDomain D.domain (Y b) (l b) (hl b)
            (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (target b) (D.pel.albanesePullback hg form)) := by
  obtain ⟨Y, a, f, l, hl, _hf, _hs, ha, _hl, htrace⟩ :=
    D.exists_clearedBranchTrace_models hg j X component cover hcover w
  let n := Intrinsic.Hecke.clearingExponent D.pel.reference.distinguished w
  let shift := IteratedSchemePullback.schemeEndPower (D.complexMarkingShift A).inv n
  let u := hA.centralUnit.unit
  have hu : (u : D.pel.EndQ) = A.algebraAction (A.basis (AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType.central s)) :=
    hA.centralUnit.unit_spec
  refine ⟨Y, (fun b => (a b ≫ (Correspondence).target) ≫ shift), l, hl, ?_, ?_⟩
  · intro b x
    change l b x ≫ ((a b ≫ (Correspondence).target) ≫ shift) = _
    rw [← Category.assoc, ← Category.assoc, ha]
    exact IteratedSchemePullback.schemeEndPower_complexPoints (D.complexMarkingShift A).inv n
      (b.lift x ≫ (Correspondence).target)
  · intro form
    let shifted := D.rationalFormsPullback hg ((↑u⁻¹ : D.pel.EndQ) ^ n) form
    have hshift : D.pel.albanesePullback hg shifted =
        AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback shift (D.pel.albanesePullback hg form) :=
      (D.centralInverseForms_power_markingShift hg hgood hIsogenyQuotient A hA u hu n form).trans
        (IteratedSchemePullback.formsPullback_schemeEndPower (D.complexMarkingShift A).inv n
          (D.pel.albanesePullback hg form)).symm
    have hactive := congrArg (fun F : Module.End ℂ D.pel.OneFormsA => F form)
      (D.activeForms_clearing hg hgood hIsogenyQuotient A hA u hu w)
    change D.heckeRationalForms hg A (A.basis (Intrinsic.Hecke.activeType D.pel.reference.distinguished w)) form =
      D.pel.pullbackForms (A.integral (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished w)) shifted at hactive
    rw [hactive]
    have ht := htrace (D.pel.albanesePullback hg shifted)
      (D.pel.albanesePullback hg
        (D.pel.pullbackForms (A.integral (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished w)) shifted))
      (hA.forms (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished w) shifted)
    rw [hshift] at ht
    simpa only [AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_comp, LinearMap.comp_apply] using ht

end ActiveHeckeThetaData

end

end OAI.RepresentationTheory.Theta.Geometric.Active.BranchTraceModels
