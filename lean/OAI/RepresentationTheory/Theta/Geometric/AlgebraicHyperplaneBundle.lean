import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace

/-! # Algebraic Hyperplane Bundle -/

namespace OAI.RepresentationTheory.Theta.Geometric.AlgebraicHyperplaneBundle

noncomputable section

/-! The existing concrete projective twists, expressed as the actual
line bundles used by the native PEL polarization definition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def lineBundleOfInvertible {X : Scheme.{u}} (M : X.Modules) (hM : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.IsInvertible M) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X where
  sheaf := M
  locallyTrivial x := by
    obtain ⟨I, U, hU, he⟩ := hM
    have hx : x ∈ iSup U := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨U i, hi, he i⟩

def algebraicHyperplaneBundle (n : ℕ) : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) :=
  lineBundleOfInvertible (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) (0 : Fin (n + 1)) 1)
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist_isInvertible (0 : Fin (n + 1)) 1)

def algebraicHyperplanePullback {X : Scheme} {n : ℕ} (f : X ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace n) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback f (algebraicHyperplaneBundle n)

end

end OAI.RepresentationTheory.Theta.Geometric.AlgebraicHyperplaneBundle
