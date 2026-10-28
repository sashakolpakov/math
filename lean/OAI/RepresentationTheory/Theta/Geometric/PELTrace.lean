import OAI.RepresentationTheory.Theta.Geometric.TateComparison
import OAI.RepresentationTheory.Theta.Geometric.DifferentialNaturality

/-! # PEL Trace -/

namespace OAI.RepresentationTheory.Theta.Geometric.PELTrace

noncomputable section

/-! The exact TateComparison Albanese trace conclusion, transported by the constructed
Kähler-to-period differential. No trace/period identity is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem albanese_trace_in_period_coordinates
    {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient)
    (A : TateComparison.Action D) (hA : A.IsRealization D hg hq hIsogenyQuotient)
    (t : AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType s) (ω : D.OneFormsA) (x : LinearTheta.BallCoordinates)
    (p : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (DifferentialNaturality.periodTest x) ⟶ D.complexSpace)
    (n : ℕ) (e : (D.complexCorrespondence t).BranchSplitting p n) :
    DifferentialNaturality.formInPeriodCoordinates x p (D.albanesePullback hg (D.pullbackForms (A.integral t) ω)) =
      ∑ i : Fin n, DifferentialNaturality.formInPeriodCoordinates x
        ((D.complexCorrespondence t).endpoint ((D.complexCorrespondence t).splitBranch p e i))
        (D.albanesePullback hg ω) :=
  DifferentialNaturality.trace_in_period_coordinates (D.complexCorrespondence t)
    (D.albanesePullback hg ω) _ (hA.forms t ω) x p n e

end

end OAI.RepresentationTheory.Theta.Geometric.PELTrace
