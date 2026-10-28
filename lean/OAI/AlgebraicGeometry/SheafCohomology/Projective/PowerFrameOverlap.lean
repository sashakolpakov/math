import OAI.AlgebraicGeometry.SheafCohomology.Projective.PowerFrameRestriction

/-! # Power Frame Overlap -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PowerFrameOverlap.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-! Tensor powers preserve the transition law between frames on overlapping opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem coordinateHyperplanePoleSheafPowerTrivializationOf_overlap
    {U V W : (Proj (homogeneousSubmodule σ R)).Opens}
    (hU : W ≤ U) (hV : W ≤ V) (j : σ)
    (e : (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j).restrict U.ι ≅
      Invertible.Scheme.Modules.unitObj U.toScheme)
    (g : (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j).restrict V.ι ≅
      Invertible.Scheme.Modules.unitObj V.toScheme)
    (r : Γ(W.toScheme, ⊤))
    (h : (OpenFrames.Scheme.Modules.restrictOpenTrivialization hU e).hom =
      (OpenFrames.Scheme.Modules.restrictOpenTrivialization hV g).hom ≫
        UnitScalar.unitEndomorphismOfTopSection r) (n : ℕ) :
    (OpenFrames.Scheme.Modules.restrictOpenTrivialization hU
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivializationOf U j e n)).hom =
    (OpenFrames.Scheme.Modules.restrictOpenTrivialization hV
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivializationOf V j g n)).hom ≫
        UnitScalar.unitEndomorphismOfTopSection (r ^ n) := by
  rw [PowerFrameRestriction.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivializationOf_restrictOpen,
    PowerFrameRestriction.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivializationOf_restrictOpen]
  exact TwistFrameScalar.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivializationOf_scalar W j _ _ r h n

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PowerFrameOverlap.MvPolynomial
