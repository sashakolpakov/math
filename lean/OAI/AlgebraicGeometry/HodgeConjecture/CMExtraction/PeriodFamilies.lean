import OAI.RepresentationTheory.Theta.Geometric.Geometry
import OAI.RepresentationTheory.Theta.Geometric.DifferentialNaturality

/-! # Period Families -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodFamilies

noncomputable section

/-! A family of actual affine points with differentiable coordinates gives an actual period test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (A : CommAlgCat.{0} ℂ) (x : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates)
  (g : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates → Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)
  (hg : ∀ a : A, DifferentiableAt ℂ (fun y => g y a) x)

def coordinateFamilyHom : A →ₐ[ℂ] RepresentationTheory.Theta.Geometric.DifferentialNaturality.functionsAt x where
  toFun a := ⟨fun y => g y a, hg a⟩
  map_zero' := Subtype.ext (funext fun y => map_zero (g y))
  map_one' := Subtype.ext (funext fun y => map_one (g y))
  map_add' a b := Subtype.ext (funext fun y => map_add (g y) a b)
  map_mul' a b := Subtype.ext (funext fun y => map_mul (g y) a b)
  commutes' c := Subtype.ext (funext fun y => (g y).commutes c)

def familyTest {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (i : AbelianScheme.TateComparison.FormConstants.affineComplexTest A ⟶ X) :
    AbelianScheme.TateComparison.FormConstants.affineComplexTest (RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodTest x) ⟶ X :=
  AbelianScheme.TateComparison.FormConstants.affineComplexMap (CommAlgCat.ofHom (coordinateFamilyHom A x g hg)) ≫ i

theorem familyTest_point {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (i : AbelianScheme.TateComparison.FormConstants.affineComplexTest A ⟶ X)
    (y : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) :
    RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.periodTestPoint x y (familyTest A x g hg i) =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (g y) := by
  let f := AbelianScheme.TateComparison.FormConstants.affineComplexMap (CommAlgCat.ofHom (coordinateFamilyHom A x g hg))
  let ev := (Pi.evalAlgHom ℂ (fun _ : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates => ℂ) y).comp (RepresentationTheory.Theta.Geometric.DifferentialNaturality.functionsAt x).val
  have h : ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv (RepresentationTheory.Theta.Geometric.DifferentialNaturality.functionsAt x) ev ≫ f = ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A (g y) :=
    (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv_comap (coordinateFamilyHom A x g hg) ev).symm
  exact (Category.assoc _ f i).symm.trans (congrArg (· ≫ i) h)

theorem familyTest_differential {X : Over Foundations.Scheme.ProjectiveSpace.complexBase} (i : AbelianScheme.TateComparison.FormConstants.affineComplexTest A ⟶ X)
    (form : AbelianScheme.TateComparison.FormConstants.OneForms X) :
    RepresentationTheory.Theta.Geometric.DifferentialNaturality.formInPeriodCoordinates x (familyTest A x g hg i) form =
      RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodDifferential x (AbelianScheme.TateComparison.FormConstants.differentialMap (CommAlgCat.ofHom (coordinateFamilyHom A x g hg))
        (form.val A i)) :=
  congrArg (RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodDifferential x)
    (form.property A (RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodTest x) (CommAlgCat.ofHom (coordinateFamilyHom A x g hg)) i).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodFamilies
