import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.TwistLineBundles

/-! # Zero Line Bundles -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ZeroLineBundles

noncomputable section

/-! All line bundles on zero-dimensional projective space over a
field are isomorphic, as follows from the actual twist classification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (K : Type u) [Field K]

theorem projectiveZeroLineCommonExponent (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Proj (Hilbert.Polynomial.GradedHilbert.grading K 0))) :
    LineCommonExponent.projectiveLineCommonExponent K L = 0 := by
  simp only [LineCommonExponent.projectiveLineCommonExponent, Nat.lt_irrefl, ↓reduceDIte]

theorem projectiveZeroLineBundles_iso (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Proj (Hilbert.Polynomial.GradedHilbert.grading K 0))) :
    Nonempty (L.sheaf ≅ M.sheaf) := by
  have hL : -LineCommonExponent.projectiveLineCommonExponent K L = 0 := by rw [projectiveZeroLineCommonExponent, neg_zero]
  have hM : -LineCommonExponent.projectiveLineCommonExponent K M = 0 := by rw [projectiveZeroLineCommonExponent, neg_zero]
  let eL := LineTwistClassification.projectiveLineBundleTwistIso K L ≪≫
    eqToIso (congrArg (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := K) (0 : Fin 1)) hL)
  let eM := LineTwistClassification.projectiveLineBundleTwistIso K M ≪≫
    eqToIso (congrArg (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := K) (0 : Fin 1)) hM)
  exact ⟨eL ≪≫ eM.symm⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ZeroLineBundles
