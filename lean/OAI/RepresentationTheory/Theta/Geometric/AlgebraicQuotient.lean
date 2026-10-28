import OAI.RepresentationTheory.Theta.Geometric.AlgebraicHyperplaneBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineBundles

/-! # Algebraic Quotient -/

namespace OAI.RepresentationTheory.Theta.Geometric.AlgebraicQuotient

noncomputable section

/-! Native algebraic twists and the quotient of two hyperplane pullbacks.
The analytic identification with the original polarization is separate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def algebraicTwistBundle (n : ℕ) (d : ℤ) : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) :=
  AlgebraicHyperplaneBundle.lineBundleOfInvertible (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) (0 : Fin (n + 1)) d)
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist_isInvertible (0 : Fin (n + 1)) d)

def algebraicTwistFrame (n : ℕ) (d : ℤ) (i : Fin (n + 1)) :
    (Scheme.Modules.pullback (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) i).ι).obj
      (algebraicTwistBundle n d).sheaf ≅
        AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := ℂ) i).toScheme :=
  AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackIsoOfRestrictIso _ _ (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization i 0 d)

def algebraicThetaQuotient {X : Scheme} {n m : ℕ}
    (f : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (g : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace m) : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X :=
  (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback g (algebraicTwistBundle m 1)).tensor
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f (algebraicTwistBundle n (-1)))

end

end OAI.RepresentationTheory.Theta.Geometric.AlgebraicQuotient
