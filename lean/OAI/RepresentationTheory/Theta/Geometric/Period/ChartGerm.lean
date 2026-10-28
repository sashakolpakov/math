import OAI.RepresentationTheory.Theta.Geometric.Period.TestDensity
import OAI.RepresentationTheory.Theta.Geometric.Period.GermRetraction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials

/-! # Chart Germ -/

namespace OAI.RepresentationTheory.Theta.Geometric.Period.ChartGerm

noncomputable section

section

/-! The first-order point, and hence every algebraic one-form evaluated
in period coordinates, depends only on the actual complex-point germ. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Filter
open scoped _root_.Topology

theorem periodEvaluationPoint_retraction (x y : LinearTheta.BallCoordinates)
    (S : Set LinearTheta.BallCoordinates) (hS : S ∈ 𝓝 x) :
    TestDensity.periodEvaluationPoint x y ≫ AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexMap (CommAlgCat.ofHom (GermRetraction.periodGermRetraction x S hS)) =
      TestDensity.periodEvaluationPoint x (GermRetraction.periodNeighborhoodRetraction x S y) := by
  exact (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv_comap (GermRetraction.periodGermRetraction x S hS)
    ((Pi.evalAlgHom ℂ (fun _ : LinearTheta.BallCoordinates => ℂ) y).comp (DifferentialNaturality.functionsAt x).val)).symm

theorem firstOrderPoint_retraction {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (x u : LinearTheta.BallCoordinates)
    (S : Set LinearTheta.BallCoordinates) (hS : S ∈ 𝓝 x)
    (p : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (DifferentialNaturality.periodTest x) ⟶ X) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.firstOrderPoint x u
      (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexMap (CommAlgCat.ofHom (GermRetraction.periodGermRetraction x S hS)) ≫ p) =
      AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.firstOrderPoint x u p := by
  have he : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexMap (CommAlgCat.ofHom (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJets.firstOrderEvaluation x u)) ≫
      AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexMap (CommAlgCat.ofHom (GermRetraction.periodGermRetraction x S hS)) =
      AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexMap (CommAlgCat.ofHom (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJets.firstOrderEvaluation x u)) := by
    apply Over.OverMorphism.ext
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (GermRetraction.periodGermRetraction_firstOrder x u S hS)
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) he)

theorem firstOrderPoint_germ {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsSeparated X.hom]
    (x u : LinearTheta.BallCoordinates) (p q : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (DifferentialNaturality.periodTest x) ⟶ X)
    (h : (fun y => TestDensity.periodEvaluationPoint x y ≫ p) =ᶠ[𝓝 x]
      (fun y => TestDensity.periodEvaluationPoint x y ≫ q)) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.firstOrderPoint x u p = AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.firstOrderPoint x u q := by
  classical
  let S := {y | TestDensity.periodEvaluationPoint x y ≫ p = TestDensity.periodEvaluationPoint x y ≫ q}
  have hS : S ∈ 𝓝 x := h
  let r := AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexMap (CommAlgCat.ofHom (GermRetraction.periodGermRetraction x S hS))
  have he : r ≫ p = r ≫ q := by
    apply TestDensity.periodTestMap_ext x
    intro y
    rw [← Category.assoc, ← Category.assoc, periodEvaluationPoint_retraction]
    by_cases hy : y ∈ S
    · simpa only [GermRetraction.periodNeighborhoodRetraction, ite_eq_left hy] using
        (show TestDensity.periodEvaluationPoint x y ≫ p = TestDensity.periodEvaluationPoint x y ≫ q from hy)
    · simpa only [GermRetraction.periodNeighborhoodRetraction, ite_eq_right hy] using h.eq_of_nhds
  exact (firstOrderPoint_retraction x u S hS p).symm.trans
    ((congrArg (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.firstOrderPoint x u) he).trans
      (firstOrderPoint_retraction x u S hS q))

theorem formInPeriodCoordinates_germ {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsSeparated X.hom]
    (x : LinearTheta.BallCoordinates) (p q : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (DifferentialNaturality.periodTest x) ⟶ X)
    (h : (fun y => TestDensity.periodEvaluationPoint x y ≫ p) =ᶠ[𝓝 x]
      (fun y => TestDensity.periodEvaluationPoint x y ≫ q)) (form : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms X) :
    DifferentialNaturality.formInPeriodCoordinates x p form = DifferentialNaturality.formInPeriodCoordinates x q form := by
  ext u
  rw [AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.formInPeriodCoordinates_firstOrder,
    AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.formInPeriodCoordinates_firstOrder, firstOrderPoint_germ x u p q h]

end

/-! Actual point germs determine the value and functoriality of their
first-order affine tests on every open period domain. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Filter
open scoped _root_.Topology

theorem periodGerm_firstOrder_value
    (Ω : TopologicalSpace.Opens LinearTheta.BallCoordinates) {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (c : Ω → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (x : Ω) (u : LinearTheta.BallCoordinates)
    (p : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (DifferentialNaturality.periodTest x.val) ⟶ X)
    (hp : ∀ᶠ y in 𝓝 x.val, ∀ hy : y ∈ Ω, TestDensity.periodEvaluationPoint x.val y ≫ p = c ⟨y, hy⟩) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint ≫ AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.firstOrderPoint x.val u p = c x :=
  (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.firstOrderPoint_value x.val u p).trans (hp.self_of_nhds x.property)

theorem periodGerm_firstOrder_comp
    (Ω : TopologicalSpace.Opens LinearTheta.BallCoordinates) {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsSeparated Y.hom]
    (f : X ⟶ Y) (c : Ω → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (d : Ω → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
    (hcd : ∀ z, c z ≫ f = d z) (x : Ω) (u : LinearTheta.BallCoordinates)
    (p : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (DifferentialNaturality.periodTest x.val) ⟶ X)
    (q : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest (DifferentialNaturality.periodTest x.val) ⟶ Y)
    (hp : ∀ᶠ y in 𝓝 x.val, ∀ hy : y ∈ Ω, TestDensity.periodEvaluationPoint x.val y ≫ p = c ⟨y, hy⟩)
    (hq : ∀ᶠ y in 𝓝 x.val, ∀ hy : y ∈ Ω, TestDensity.periodEvaluationPoint x.val y ≫ q = d ⟨y, hy⟩) :
    AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.firstOrderPoint x.val u p ≫ f = AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.firstOrderPoint x.val u q := by
  have h : (fun y => TestDensity.periodEvaluationPoint x.val y ≫ (p ≫ f)) =ᶠ[𝓝 x.val]
      (fun y => TestDensity.periodEvaluationPoint x.val y ≫ q) := by
    filter_upwards [hp, hq, Ω.isOpen.mem_nhds x.property] with y hpy hqy hy
    exact (Category.assoc _ p f).symm.trans
      ((congrArg (· ≫ f) (hpy hy)).trans ((hcd ⟨y, hy⟩).trans (hqy hy).symm))
  exact (Category.assoc _ p f).trans (firstOrderPoint_germ x.val u (p ≫ f) q h)

end

end OAI.RepresentationTheory.Theta.Geometric.Period.ChartGerm
