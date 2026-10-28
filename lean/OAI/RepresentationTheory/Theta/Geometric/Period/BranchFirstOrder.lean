import OAI.RepresentationTheory.Theta.Geometric.Period.ChartGerm
import OAI.RepresentationTheory.Theta.Geometric.Dual.BranchReduction

/-! # Branch First Order -/

namespace OAI.RepresentationTheory.Theta.Geometric.Period.BranchFirstOrder

noncomputable section

/-! The derivative of an actual holomorphic period branch is the unique
dual-number branch used by the algebraic trace. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Filter
open scoped _root_.Topology

theorem dualBranchLift_of_period_germs
    (Ω : TopologicalSpace.Opens LinearTheta.BallCoordinates) {X Y Z : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsSeparated X.hom]
    (C : AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence Z) (m : X ⟶ Z) (a : Y ⟶ C.cover) (f : Y ⟶ X)
    (hsquare : a ≫ C.source = f ≫ m)
    (c : Ω → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (d : Ω → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
    (hcd : ∀ z, d z ≫ f = c z) (x : Ω) (u : LinearTheta.BallCoordinates)
    (p : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (DifferentialNaturality.periodTest x.val) ⟶ X)
    (q : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (DifferentialNaturality.periodTest x.val) ⟶ Y)
    (hp : ∀ᶠ y in 𝓝 x.val, ∀ hy : y ∈ Ω, TestDensity.periodEvaluationPoint x.val y ≫ p = c ⟨y, hy⟩)
    (hq : ∀ᶠ y in 𝓝 x.val, ∀ hy : y ∈ Ω, TestDensity.periodEvaluationPoint x.val y ≫ q = d ⟨y, hy⟩)
    (b : C.Fiber (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint ≫ (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.firstOrderPoint x.val u p ≫ m)))
    (hb : b.val = d x ≫ a) :
    (Dual.BranchReduction.dualBranchLift C (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.firstOrderPoint x.val u p ≫ m) b).val =
      AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.firstOrderPoint x.val u q ≫ a := by
  let t := AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.firstOrderPoint x.val u p ≫ m
  have hsource : (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.firstOrderPoint x.val u q ≫ a) ≫ C.source = t := by
    rw [Category.assoc, hsquare, ← Category.assoc]
    exact congrArg (· ≫ m) (ChartGerm.periodGerm_firstOrder_comp Ω f d c hcd x u q p hq hp)
  let l : C.Fiber t := ⟨AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.firstOrderPoint x.val u q ≫ a, hsource⟩
  have hl : Dual.BranchReduction.branchRestriction C t AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint l = b := by
    apply Subtype.ext
    change AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint ≫ (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.firstOrderPoint x.val u q ≫ a) = b.val
    rw [← Category.assoc, ChartGerm.periodGerm_firstOrder_value Ω d x u q hq, hb]
  exact congrArg Subtype.val ((Dual.BranchReduction.dualBranchReduction_bijective C t).1
    ((Dual.BranchReduction.dualBranchLift_reduction C t b).trans hl.symm))

theorem dualBranchForm_of_period_germs
    (Ω : TopologicalSpace.Opens LinearTheta.BallCoordinates) {X Y Z : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsSeparated X.hom]
    (C : AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence Z) (m : X ⟶ Z) (a : Y ⟶ C.cover) (f : Y ⟶ X)
    (hsquare : a ≫ C.source = f ≫ m)
    (c : Ω → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (d : Ω → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
    (hcd : ∀ z, d z ≫ f = c z) (x : Ω) (u : LinearTheta.BallCoordinates)
    (p : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (DifferentialNaturality.periodTest x.val) ⟶ X)
    (q : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (DifferentialNaturality.periodTest x.val) ⟶ Y)
    (hp : ∀ᶠ y in 𝓝 x.val, ∀ hy : y ∈ Ω, TestDensity.periodEvaluationPoint x.val y ≫ p = c ⟨y, hy⟩)
    (hq : ∀ᶠ y in 𝓝 x.val, ∀ hy : y ∈ Ω, TestDensity.periodEvaluationPoint x.val y ≫ q = d ⟨y, hy⟩)
    (b : C.Fiber (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint ≫ (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.firstOrderPoint x.val u p ≫ m)))
    (hb : b.val = d x ≫ a) (form : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms Z) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.dualDifferential (form.val AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest
      (C.endpoint (Dual.BranchReduction.dualBranchLift C (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.firstOrderPoint x.val u p ≫ m) b))) =
      DifferentialNaturality.formInPeriodCoordinates x.val q (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (a ≫ C.target) form) u := by
  rw [AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.formInPeriodCoordinates_firstOrder]
  change AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.dualDifferential (form.val AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest
    ((Dual.BranchReduction.dualBranchLift C (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.firstOrderPoint x.val u p ≫ m) b).val ≫ C.target)) =
    AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.dualDifferential (form.val AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.firstOrderPoint x.val u q ≫ (a ≫ C.target)))
  rw [dualBranchLift_of_period_germs Ω C m a f hsquare c d hcd x u p q hp hq b hb,
    Category.assoc]

end

end OAI.RepresentationTheory.Theta.Geometric.Period.BranchFirstOrder
