import OAI.RepresentationTheory.Theta.Geometric.Period.ChartGerm
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseProjectivity
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicForms

/-! # Canonical Period Germs -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! All actual period charts with the prescribed germ give the same
period covector for an algebraic Albanese form. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseProjectivity Filter
open scoped _root_.Topology

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.canonicalPeriodChart_form_eq (hg : D.pel.HasIntegralModelGeometry)
    (c : D.domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace) (x : D.domain)
    (p q : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (DifferentialNaturality.periodTest x.val) ⟶ D.pel.complexSpace)
    (hp : D.IsPeriodChartAt c x p) (hq : D.IsPeriodChartAt c x q)
    (form : D.pel.OneFormsA) :
    DifferentialNaturality.formInPeriodCoordinates x.val p (D.pel.albanesePullback hg form) =
      DifferentialNaturality.formInPeriodCoordinates x.val q (D.pel.albanesePullback hg form) := by
  let A := D.pel.actualComplexAlbaneseVariety hg
  let : A.toOver.left.IsSeparated := AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntrinsicForms.integralProjective_separated A.variety
  let : IsSeparated D.pel.complexAlbanese.X.hom := inferInstanceAs (IsSeparated A.toOver.hom)
  change DifferentialNaturality.formInPeriodCoordinates x.val (p ≫ D.pel.complexAlbaneseMap hg) form =
    DifferentialNaturality.formInPeriodCoordinates x.val (q ≫ D.pel.complexAlbaneseMap hg) form
  apply Period.ChartGerm.formInPeriodCoordinates_germ
  filter_upwards [hp, hq, D.domain.isOpen.mem_nhds x.property] with y hpy hqy hy
  exact (Category.assoc _ p _).symm.trans
    ((congrArg (· ≫ D.pel.complexAlbaneseMap hg) ((hpy hy).trans (hqy hy).symm)).trans
      (Category.assoc _ q _))

end

end OAI.RepresentationTheory.Theta.Geometric
