import OAI.RepresentationTheory.Theta.Geometric.Projective.BranchLift
import OAI.RepresentationTheory.Theta.Geometric.Period.AlgebraicTrace

/-! # Continuous Branch Trace -/

namespace OAI.RepresentationTheory.Theta.Geometric.ContinuousBranchTrace

noncomputable section

/-! A complete continuous family of actual finite étale branches has
constructed projective holomorphic models, and its smooth trace agrees
with TateComparison's algebraic trace for every algebraic one-form. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

theorem exists_continuousBranchTrace_models
    (Ω : TopologicalSpace.Opens LinearTheta.BallCoordinates) [PreconnectedSpace Ω] [Nonempty Ω]
    (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {Z : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (m : X.toOver ⟶ Z) [IsOpenImmersion m.left] (C : AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence Z)
    (c : Ω → X.analyticSpace) (hc : ContMDiff 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, X.analyticModel) ∞ c)
    (I : Type) [Fintype I] (b : I → C(Ω, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints C.cover))
    (hb : ∀ i x, b i x ≫ C.source = c x ≫ m)
    (hbij : ∀ x, Function.Bijective (fun i : I => (⟨b i x, hb i x⟩ : C.Fiber (c x ≫ m)))) :
    ∃ (Y : I → AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (a : ∀ i, (Y i).toOver ⟶ C.cover)
      (f : ∀ i, (Y i).toOver ⟶ X.toOver) (l : ∀ i, Ω → (Y i).analyticSpace)
      (hl : ∀ i, ContMDiff 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, (Y i).analyticModel) ∞ (l i)),
      (∀ i, IsFinite (f i).left ∧ Etale (f i).left) ∧
      (∀ i, a i ≫ C.source = f i ≫ m) ∧
      (∀ i x, l i x ≫ a i = b i x) ∧ (∀ i x, l i x ≫ f i = c x) ∧
      ∀ (form other : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms Z), AlgebraicGeometry.AbelianScheme.TateComparison.Branches.IsBranchTrace C form other →
        Projective.FormOnDomain.projectiveFormOnDomain Ω X c hc (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback m other) =
          ∑ i : I, Projective.FormOnDomain.projectiveFormOnDomain Ω (Y i) (l i) (hl i)
            (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (a i ≫ C.target) form) := by
  choose Y a f l hfin het hl hsquare hbranch hsource using
    fun i => Projective.BranchLift.exists_projective_holomorphic_branch_lift Ω X m C c hc (b i) (hb i)
  refine ⟨Y, a, f, l, hl, fun i => ⟨hfin i, het i⟩, hsquare, hbranch, hsource, ?_⟩
  intro form other htrace
  apply Period.AlgebraicTrace.periodTrace_algebraicBranches Ω X m C c hc I Y a f l hl hsquare hsource _ form other htrace
  intro x
  exact ⟨Equiv.ofBijective (fun i : I => (⟨b i x, hb i x⟩ : C.Fiber (c x ≫ m))) (hbij x),
    fun i => (hbranch i x).symm⟩

end

end OAI.RepresentationTheory.Theta.Geometric.ContinuousBranchTrace
