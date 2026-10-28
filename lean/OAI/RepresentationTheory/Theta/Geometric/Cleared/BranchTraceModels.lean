import OAI.RepresentationTheory.Theta.Geometric.ContinuousBranchTrace
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.ClearedBranchFibers
import OAI.RepresentationTheory.Theta.Geometric.ComponentFormFaithfulness

/-! # Branch Trace Models -/

namespace OAI.RepresentationTheory.Theta.Geometric.Cleared.BranchTraceModels

noncomputable section

/-! The original cleared correspondence branches supply their actual
projective holomorphic models and the algebraic trace comparison. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

namespace ActiveHeckeThetaData

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (j : Fin D.pel.componentCount)
    (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (component : X.toOver ≅ D.componentComplex j)
    (cover : D.domain → X.analyticSpace) (hcover : D.IsPeriodUniformization X cover)
    (w : Intrinsic.Hecke.ActiveWeight)

local notation "Branches" => D.ClearedBranch (D.totalPeriodMap j X component cover) w
local notation "Correspondence" => D.pel.complexCorrespondence (OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished w)

include hg in
theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.exists_clearedBranchTrace_models
    [Fintype (D.ClearedBranch (D.totalPeriodMap j X component cover) w)] :
    let hc := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hcover.2.2.1
    ∃ (Y : Branches → AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
      (a : ∀ b, (Y b).toOver ⟶ (Correspondence).cover)
      (f : ∀ b, (Y b).toOver ⟶ X.toOver) (l : ∀ b, D.domain → (Y b).analyticSpace)
      (hl : ∀ b, ContMDiff 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, (Y b).analyticModel) ∞ (l b)),
      (∀ b, IsFinite (f b).left ∧ Etale (f b).left) ∧
      (∀ b, a b ≫ (Correspondence).source = f b ≫ (component.hom ≫ D.componentComplexInclusion j)) ∧
      (∀ b x, l b x ≫ a b = b.lift x) ∧ (∀ b x, l b x ≫ f b = cover x) ∧
      ∀ (form other : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms D.pel.complexSpace), AlgebraicGeometry.AbelianScheme.TateComparison.Branches.IsBranchTrace Correspondence form other →
        Projective.FormOnDomain.projectiveFormOnDomain D.domain X cover hc
          (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (component.hom ≫ D.componentComplexInclusion j) other) =
          ∑ b : Branches, Projective.FormOnDomain.projectiveFormOnDomain D.domain (Y b) (l b) (hl b)
            (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (a b ≫ (Correspondence).target) form) := by
  let hc := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold.Constructions.HolomorphicManifoldRegularity.contMDiff_of_mdifferentiable hcover.2.2.1
  let : ContractibleSpace D.domain := D.domain_contractible hg
  let : Nonempty D.domain := ⟨D.domainOrigin hg⟩
  let : IsIso component.hom.left := inferInstanceAs (IsIso ((Over.forget AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase).map component.hom))
  let : IsOpenImmersion (D.componentComplexInclusion j).left := D.componentComplexInclusion_open hg j
  let m := component.hom ≫ D.componentComplexInclusion j
  let : IsOpenImmersion m.left := inferInstanceAs (IsOpenImmersion (component.hom.left ≫ (D.componentComplexInclusion j).left))
  apply ContinuousBranchTrace.exists_continuousBranchTrace_models D.domain X m Correspondence cover hc
    Branches (fun b => b.lift) (fun b x => b.source x)
  intro x
  exact (D.nativeClearedBranchFiberEquiv hg
    (D.totalPeriodMap_continuous j X component cover hc.continuous) w x).bijective

end ActiveHeckeThetaData

end

end OAI.RepresentationTheory.Theta.Geometric.Cleared.BranchTraceModels
