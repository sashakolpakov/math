import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJets
import OAI.RepresentationTheory.Theta.Geometric.Geometry
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointUnderlying

/-! # Period Jet -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet

noncomputable section

/-! A genuine first-order period test factors through every open neighborhood of its value. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.RepresentationTheory.Theta.Geometric.Geometry

abbrev dualTest : CommAlgCat.{0} ℂ := .of ℂ (DualNumber ℂ)

def dualClosedPoint : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (AbelianScheme.TateComparison.FormConstants.affineComplexTest dualTest) :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (DualNumber ℂ) (TrivSqZeroExt.fstHom ℂ ℂ ℂ)

def firstOrderPoint {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (x u : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates)
    (p : AbelianScheme.TateComparison.FormConstants.affineComplexTest (RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodTest x) ⟶ X) : AbelianScheme.TateComparison.FormConstants.affineComplexTest dualTest ⟶ X :=
  AbelianScheme.TateComparison.FormConstants.affineComplexMap (CommAlgCat.ofHom (PeriodJets.firstOrderEvaluation x u)) ≫ p

theorem firstOrderPoint_value {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (x u : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates)
    (p : AbelianScheme.TateComparison.FormConstants.affineComplexTest (RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodTest x) ⟶ X) :
    dualClosedPoint ≫ firstOrderPoint x u p = RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.periodTestPoint x x p := by
  let f := AbelianScheme.TateComparison.FormConstants.affineComplexMap (CommAlgCat.ofHom (PeriodJets.firstOrderEvaluation x u))
  have h : dualClosedPoint ≫ f = ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (RepresentationTheory.Theta.Geometric.DifferentialNaturality.functionsAt x) (RepresentationTheory.Theta.Geometric.DifferentialNaturality.evaluateAt x) :=
    (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv_comap (PeriodJets.firstOrderEvaluation x u) (TrivSqZeroExt.fstHom ℂ ℂ ℂ)).symm
  exact (Category.assoc dualClosedPoint f p).symm.trans (congrArg (· ≫ p) h)

theorem dualTest_lift_open {X U : Over Foundations.Scheme.ProjectiveSpace.complexBase} (i : U ⟶ X)
    [IsOpenImmersion i.left] (t : AbelianScheme.TateComparison.FormConstants.affineComplexTest dualTest ⟶ X)
    (ht : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (dualClosedPoint ≫ t) ∈ Set.range i.left) :
    ∃ l : AbelianScheme.TateComparison.FormConstants.affineComplexTest dualTest ⟶ U, l ≫ i = t := by
  let : Subsingleton (AbelianScheme.TateComparison.FormConstants.affineComplexTest dualTest).left := by
    change Subsingleton (PrimeSpectrum (DualNumber ℂ))
    exact PeriodJets.dualNumberSpectrum_subsingleton
  let x₀ := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying dualClosedPoint
  have hr : Set.range t.left ⊆ Set.range i.left := by
    rintro _ ⟨z, rfl⟩
    have hz : z = x₀ := Subsingleton.elim _ _
    rw [hz]
    exact ht
  let l := IsOpenImmersion.lift i.left t.left hr
  have hl : l ≫ i.left = t.left := IsOpenImmersion.lift_fac i.left t.left hr
  have hw : l ≫ U.hom = (AbelianScheme.TateComparison.FormConstants.affineComplexTest dualTest).hom := by
    rw [← i.w, ← Category.assoc, hl]
    exact t.w
  refine ⟨Over.homMk l hw, ?_⟩
  exact Over.OverMorphism.ext hl

theorem firstOrderPoint_lift_open {X U : Over Foundations.Scheme.ProjectiveSpace.complexBase} (i : U ⟶ X)
    [IsOpenImmersion i.left] (x u : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates)
    (p : AbelianScheme.TateComparison.FormConstants.affineComplexTest (RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodTest x) ⟶ X)
    (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying (RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.periodTestPoint x x p) ∈
      Set.range i.left) :
    ∃ l : AbelianScheme.TateComparison.FormConstants.affineComplexTest dualTest ⟶ U, l ≫ i = firstOrderPoint x u p := by
  apply dualTest_lift_open i
  rw [firstOrderPoint_value]
  exact hx

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet
