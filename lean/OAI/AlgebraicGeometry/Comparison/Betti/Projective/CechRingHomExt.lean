import OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech

/-! # Cech Ring Hom Ext -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechRingHomExt.Dolbeault

noncomputable section

/-! Ring maps out of an original projective intersection are determined on its first affine chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u v

variable {R : Type u} [CommRing R] {σ : Type} {S : Type v} [CommSemiring S]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem projectiveProductAway_ringHom_ext {q : ℕ} (a : Fin (q + 1) → σ)
    (f g : HomogeneousLocalization.Away (homogeneousSubmodule σ R)
      (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) a) →+* S)
    (h : ∀ p : HomogeneousLocalization.Away (homogeneousSubmodule σ R) (X (a 0)),
      f (HomogeneousLocalization.awayMap (f := X (a 0))
        (g := SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial (R := R) a)
        (x := SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) a) (homogeneousSubmodule σ R)
        (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial_mem (R := R) a) rfl p) =
      g (HomogeneousLocalization.awayMap (f := X (a 0))
        (g := SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial (R := R) a)
        (x := SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) a) (homogeneousSubmodule σ R)
        (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial_mem (R := R) a) rfl p)) : f = g := by
  let := (HomogeneousLocalization.awayMap (f := X (a 0))
    (g := SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial (R := R) a)
    (x := SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) a) (homogeneousSubmodule σ R)
    (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial_mem (R := R) a) rfl).toAlgebra
  let t := HomogeneousLocalization.Away.isLocalizationElem
    (SheafCohomology.Projective.SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R (a 0)) (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial_mem (R := R) a)
  let : IsLocalization.Away t
      (HomogeneousLocalization.Away (homogeneousSubmodule σ R)
        (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) a)) :=
    HomogeneousLocalization.Away.isLocalization_mul
      (SheafCohomology.Projective.SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R (a 0))
      (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial_mem (R := R) a) rfl one_ne_zero
  apply IsLocalization.ringHom_ext (Submonoid.powers t)
  exact RingHom.ext h

theorem projectiveCechRingHom_ext_firstChart {q : ℕ} (a : Fin (q + 1) → ULift.{u} σ)
    (f g : Γ(Proj (homogeneousSubmodule σ R), SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a) →+* S)
    (h : ∀ s : Γ(Proj (homogeneousSubmodule σ R), SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (a 0)),
      f ((Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a 0)).op s) =
      g ((Proj (homogeneousSubmodule σ R)).presheaf.map
        (homOfLE (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a 0)).op s)) : f = g := by
  let e := (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionAwayIso (R := R) a).commRingCatIsoToRingEquiv
  have hfg : f.comp e.toRingHom = g.comp e.toRingHom := by
    apply projectiveProductAway_ringHom_ext (fun k => (a k).down)
    intro p
    have hp := ConcreteCategory.congr_hom
      (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionAwayIso_naturality_firstChart (R := R) a) p
    change e (HomogeneousLocalization.awayMap (f := X (a 0).down)
      (g := SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial (R := R) (fun k => (a k).down))
      (x := SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) (fun k => (a k).down))
      (homogeneousSubmodule σ R)
      (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial_mem (R := R) (fun k => (a k).down)) rfl p) = _ at hp
    exact (congrArg f hp).trans ((h _).trans (congrArg g hp).symm)
  apply RingHom.ext
  intro s
  have hs := DFunLike.congr_fun hfg (e.symm s)
  change f (e (e.symm s)) = g (e (e.symm s)) at hs
  simpa only [RingEquiv.apply_symm_apply] using hs

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechRingHomExt.Dolbeault
