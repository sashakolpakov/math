import OAI.AlgebraicGeometry.SheafCohomology.Projective.PowerFrameOverlap
import OAI.AlgebraicGeometry.SheafCohomology.Projective.DualFrameTransition

/-! # Power Frame Transition -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PowerFrameTransition.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-! Tensor-power transitions expressed using the frame transition relation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem coordinateHyperplanePoleSheafPowerTrivializationOf_frameTransition
    {U V W : (Proj (homogeneousSubmodule σ R)).Opens}
    (hU : W ≤ U) (hV : W ≤ V) (j : σ)
    (e : (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j).restrict U.ι ≅
      Invertible.Scheme.Modules.unitObj U.toScheme)
    (g : (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j).restrict V.ι ≅
      Invertible.Scheme.Modules.unitObj V.toScheme)
    (r : Γ(W.toScheme, ⊤))
    (h : DualFrameTransition.FrameTransition
      (OpenFrames.Scheme.Modules.restrictOpenTrivialization hU e)
      (OpenFrames.Scheme.Modules.restrictOpenTrivialization hV g)
      (UnitScalar.unitEndomorphismOfTopSection r)) (n : ℕ) :
    DualFrameTransition.FrameTransition
      (OpenFrames.Scheme.Modules.restrictOpenTrivialization hU
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivializationOf U j e n))
      (OpenFrames.Scheme.Modules.restrictOpenTrivialization hV
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivializationOf V j g n))
      (UnitScalar.unitEndomorphismOfTopSection (r ^ n)) :=
  PowerFrameOverlap.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivializationOf_overlap hU hV j e g r h n

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PowerFrameTransition.MvPolynomial
