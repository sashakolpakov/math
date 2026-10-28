import OAI.RepresentationTheory.Theta.Geometric.Pullback.OpenFrameRestriction
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneFrameTransition

/-! # Hyperplane Pullback Frames -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.HyperplanePullbackFrames

noncomputable section

/-! Native frames of a projective hyperplane pullback and their exact
overlap transitions, over an arbitrary coefficient ring. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace PolarizationEmbedding

attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type} [CommRing R] {n : ℕ} {X : Scheme.{0}}
  (a : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) (j : Fin (n + 1))

def hyperplanePullbackFrame (i : Fin (n + 1)) :
    ((Scheme.Modules.pullback a).obj (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j)).restrict
      (a ⁻¹ᵁ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).ι ≅
        SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (a ⁻¹ᵁ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).toScheme :=
  RepresentationTheory.Theta.Geometric.Pullback.Algebraic.pullbackOpenFrame a (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j)
    (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    (SheafCohomology.Projective.HyperplaneFrames.MvPolynomial.coordinateHyperplanePoleSheafTrivialization (R := R) i j)

theorem hyperplanePullbackFrame_transition (i k : Fin (n + 1)) :
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization
      (a.preimage_mono (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k))
      (hyperplanePullbackFrame a j i)).hom =
    (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization
      (a.preimage_mono (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k))
      (hyperplanePullbackFrame a j k)).hom ≫
      SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection
        ((a ∣_ SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).appTop
          ((SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).topIso.inv
            (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k))) := by
  have hl := congrArg Iso.hom
    (RepresentationTheory.Theta.Geometric.Pullback.OpenFrameRestriction.pullbackOpenFrame_restrict a (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j)
      (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)
      (SheafCohomology.Projective.HyperplaneFrames.MvPolynomial.coordinateHyperplanePoleSheafTrivialization (R := R) i j))
  have hr := congrArg Iso.hom
    (RepresentationTheory.Theta.Geometric.Pullback.OpenFrameRestriction.pullbackOpenFrame_restrict a (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j)
      (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)
      (SheafCohomology.Projective.HyperplaneFrames.MvPolynomial.coordinateHyperplanePoleSheafTrivialization (R := R) k j))
  have ht := RepresentationTheory.Theta.Geometric.Pullback.Algebraic.pullbackOpenFrame_scalar a (SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j)
    (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k) _ _ _
      (SheafCohomology.Projective.HyperplaneFrameTransition.MvPolynomial.coordinateHyperplanePole_frameTransition (R := R) i k j)
  exact hl.trans (ht.trans (congrArg (fun q => q ≫ SheafCohomology.Projective.UnitScalar.unitEndomorphismOfTopSection
    ((a ∣_ SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).appTop
      ((SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).topIso.inv
        (SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k)))) hr.symm))

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.HyperplanePullbackFrames
