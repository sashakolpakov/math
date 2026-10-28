import OAI.RepresentationTheory.Theta.Geometric.EqualFrameTransitionGluing

/-! # Coordinate Pole Iso -/

namespace OAI.RepresentationTheory.Theta.Geometric.CoordinatePoleIso

noncomputable section

section

/-! Coordinate hyperplanes give isomorphic native twists in every degree. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem coordinateTransitionTopUnit_zpow {R : Type} [CommRing R] {σ : Type}
    (i k : σ) (d : ℤ) :
    ((AlgebraicGeometry.SheafCohomology.Projective.OverlapTopUnit.MvPolynomial.coordinateOpenTransitionTopUnit (R := R) i k ^ d :
      Γ((AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme, ⊤)ˣ) :
      Γ((AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme, ⊤)) =
    (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).topIso.inv
      ((AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k ^ d :
        Γ(Proj (MvPolynomial.homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)ˣ) :
        Γ(Proj (MvPolynomial.homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)) := by
  let φ := (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).topIso.inv.hom.toMonoidHom
  change (((Units.map φ) (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k) ^ d :
    Γ((AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme, ⊤)ˣ) :
    Γ((AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme, ⊤)) = _
  rw [← map_zpow]
  rfl

theorem coordinateTwist_isomorphic {R : Type} [CommRing R] {σ : Type} (j j' : σ) (d : ℤ) :
    Nonempty (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d ≅
      AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j' d) := by
  apply EqualFrameTransitionGluing.exists_iso_of_equal_frame_transitions _ _
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R)) AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top
    (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R))
    (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R))
    (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R))
    (fun i k => le_of_eq (AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq (R := R) i k).symm)
    (fun i => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := R) i j d)
    (fun i => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := R) i j' d)
    (fun i k => ((AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k ^ d :
      Γ(Proj (MvPolynomial.homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)ˣ) :
      Γ(Proj (MvPolynomial.homogeneousSubmodule σ R), AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)))
  · intro i k
    have h := AlgebraicGeometry.SheafCohomology.Projective.IntegerTwistTransitions.MvPolynomial.coordinateHyperplaneTwistTrivialization_restrict_transition (R := R) i k j d
    rw [coordinateTransitionTopUnit_zpow] at h
    exact h
  · intro i k
    have h := AlgebraicGeometry.SheafCohomology.Projective.IntegerTwistTransitions.MvPolynomial.coordinateHyperplaneTwistTrivialization_restrict_transition (R := R) i k j' d
    rw [coordinateTransitionTopUnit_zpow] at h
    exact h

end

/-! Each coordinate-hyperplane dual is isomorphic to the fixed native O(1).
The isomorphism is glued from their actual standard frames. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory

local instance coordinatePoleMonoidal (X : Scheme) : MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

theorem coordinateTwist_iso_fixed (n : ℕ) (j : Fin (n + 1)) :
    Nonempty (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j 1 ≅
      (AlgebraicQuotient.algebraicTwistBundle n 1).sheaf) := coordinateTwist_isomorphic j 0 1

theorem coordinatePole_iso_twist (n : ℕ) (j : Fin (n + 1)) :
    Nonempty (AlgebraicGeometry.SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := ℂ) j ≅
      (AlgebraicQuotient.algebraicTwistBundle n 1).sheaf) := by
  obtain ⟨e⟩ := coordinateTwist_iso_fixed n j
  exact ⟨(λ_ (AlgebraicGeometry.SheafCohomology.Projective.HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := ℂ) j)).symm ≪≫ e⟩

end

end OAI.RepresentationTheory.Theta.Geometric.CoordinatePoleIso
