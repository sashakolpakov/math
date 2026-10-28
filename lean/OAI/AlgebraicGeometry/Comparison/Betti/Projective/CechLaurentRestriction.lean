import OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech

/-! # Cech Laurent Restriction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechLaurentRestriction.Dolbeault

noncomputable section

/-! The original affine-chart restriction has its ordinary polynomial coefficients in Laurent coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {σ : Type}

local instance projectiveCechLaurentDecEq : DecidableEq σ := Classical.decEq σ

attribute [local instance] MvPolynomial.gradedAlgebra

theorem projectiveCechLaurent_restrict_firstChart {q : ℕ} (a : Fin (q + 1) → ULift.{u} σ)
    (p : HomogeneousLocalization.Away (homogeneousSubmodule σ R) (X (a 0).down)) :
    SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a
      ((Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a 0)).op
          ((Proj.basicOpenIsoAway (homogeneousSubmodule σ R) (X (a 0).down)
            (SheafCohomology.Projective.SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R (a 0).down) one_pos).hom p)) =
      AddMonoidAlgebra.mapDomain
        (SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a k).down))).toAddMonoidHom
        (SheafCohomology.Projective.SpaceChart.MvPolynomial.chartRingEquiv R (a 0).down p) := by
  classical
  have hp := ConcreteCategory.congr_hom
    (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionAwayIso_naturality_firstChart (R := R) a) p
  refine (congrArg (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a) hp.symm).trans ?_
  change SheafCohomology.Projective.LaurentMonomialBasis.MvPolynomial.laurentMonomialRingEquiv R (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a k).down))
    (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateProductAwayRingEquiv (R := R) (fun k => (a k).down)
      ((SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionAwayIso (R := R) a).inv
        ((SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionAwayIso (R := R) a).hom _))) = _
  rw [Iso.hom_inv_id_apply]
  exact SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateProductAwayLaurentRingEquiv_awayMap (R := R) (fun k => (a k).down) p

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechLaurentRestriction.Dolbeault
