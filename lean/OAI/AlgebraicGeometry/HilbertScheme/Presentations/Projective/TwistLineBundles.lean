import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.LineTwistClassification

/-! # Twist Line Bundles -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.TwistLineBundles

noncomputable section

/-! The native integer twists are actual Presentations line bundles, with
their standard affine-chart pullback frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (K : Type u) [Field K]

def projectiveTwistLineBundle (n : ℕ) (d : ℤ) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Proj (Hilbert.Polynomial.GradedHilbert.grading K n)) where
  sheaf := SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := K) (0 : Fin (n + 1)) d
  locallyTrivial x := by
    have hx : x ∈ iSup (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K) (σ := Fin (n + 1))) := by
      rw [SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top]
      trivial
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine ⟨SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K) i, hxi, ⟨?_⟩⟩
    exact (Scheme.Modules.restrictFunctorIsoPullback (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := K) i).ι).symm.app _ ≪≫
      SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := K) i 0 d

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.TwistLineBundles
