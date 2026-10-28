import OAI.RepresentationTheory.Theta.Geometric.Projective.FormOnDomain
import OAI.RepresentationTheory.Theta.Geometric.Period.BranchFirstOrder

/-! # Algebraic Trace -/

namespace OAI.RepresentationTheory.Theta.Geometric.Period.AlgebraicTrace

noncomputable section

/-! The algebraic trace is the actual smooth sum of differentiated
holomorphic branches, with each source-fiber point included exactly once. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

theorem periodTrace_algebraicBranches
    (Ω : TopologicalSpace.Opens LinearTheta.BallCoordinates) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {Z : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (m : X.toOver ⟶ Z) (C : AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence Z)
    (c : Ω → X.analyticSpace) (hc : ContMDiff 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, X.analyticModel) ∞ c)
    (I : Type) [Fintype I] (Y : I → AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : ∀ i, (Y i).toOver ⟶ C.cover) (f : ∀ i, (Y i).toOver ⟶ X.toOver)
    (l : ∀ i, Ω → (Y i).analyticSpace)
    (hl : ∀ i, ContMDiff 𝓘(ℂ, LinearTheta.BallCoordinates) 𝓘(ℂ, (Y i).analyticModel) ∞ (l i))
    (hsquare : ∀ i, a i ≫ C.source = f i ≫ m)
    (hsource : ∀ i x, l i x ≫ f i = c x)
    (hbranches : ∀ x, ∃ β : I ≃ C.Fiber (c x ≫ m), ∀ i, (β i).val = l i x ≫ a i)
    (form other : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms Z) (htrace : AlgebraicGeometry.AbelianScheme.TateComparison.Branches.IsBranchTrace C form other) :
    Projective.FormOnDomain.projectiveFormOnDomain Ω X c hc (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback m other) =
      ∑ i : I, Projective.FormOnDomain.projectiveFormOnDomain Ω (Y i) (l i) (hl i)
        (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (a i ≫ C.target) form) := by
  let : X.toOver.left.IsSeparated := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicForms.integralProjective_separated X
  let : IsSeparated X.toOver.hom := inferInstance
  apply SmoothPullbackFaithfulness.smoothOneForm_eq_of_preferredChart
  intro x u
  change Projective.FormOnDomain.periodChartEvaluation Ω x u (Projective.FormOnDomain.projectiveFormOnDomain Ω X c hc (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback m other)) =
    Projective.FormOnDomain.periodChartEvaluation Ω x u (∑ i : I, Projective.FormOnDomain.projectiveFormOnDomain Ω (Y i) (l i) (hl i)
      (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (a i ≫ C.target) form))
  rw [map_sum]
  obtain ⟨p, hp, hpform⟩ := Projective.FormOnDomain.projectiveFormOnDomain_periodTest Ω X c hc x
  choose q hq hqform using fun i => Projective.FormOnDomain.projectiveFormOnDomain_periodTest Ω (Y i) (l i) (hl i) x
  rw [hpform]
  let t := AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.firstOrderPoint x.val u p ≫ m
  have hbase : AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint ≫ t = c x ≫ m :=
    (Category.assoc _ _ m).symm.trans
      (congrArg (· ≫ m) (ChartGerm.periodGerm_firstOrder_value Ω c x u p hp))
  have hβ : ∃ β : I ≃ C.Fiber (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint ≫ t),
      ∀ i, (β i).val = l i x ≫ a i := by
    exact (congrArg (fun z : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z =>
      ∃ β : I ≃ C.Fiber z, ∀ i, (β i).val = l i x ≫ a i) hbase).mpr (hbranches x)
  obtain ⟨β, hβ⟩ := hβ
  have ht : DifferentialNaturality.formInPeriodCoordinates x.val p (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback m other) u =
      AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.dualDifferential (other.val AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest t) := by
    change DifferentialNaturality.formInPeriodCoordinates x.val (p ≫ m) other u = _
    rw [AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.formInPeriodCoordinates_firstOrder]
    exact congrArg (fun z => AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.dualDifferential (other.val AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest z))
      (Category.assoc _ p m).symm
  refine ht.trans ((Dual.BranchReduction.dualBranchTrace_indexed C form other htrace t I β).trans ?_)
  apply Finset.sum_congr rfl
  intro i _
  exact (BranchFirstOrder.dualBranchForm_of_period_germs Ω C m (a i) (f i) (hsquare i)
    c (l i) (hsource i) x u p (q i) hp (hq i) (β i) (hβ i) form).trans
      (hqform i (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (a i ≫ C.target) form) u).symm

end

end OAI.RepresentationTheory.Theta.Geometric.Period.AlgebraicTrace
