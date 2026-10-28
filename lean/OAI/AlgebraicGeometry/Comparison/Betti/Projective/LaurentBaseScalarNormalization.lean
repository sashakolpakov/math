import OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech

/-! # Laurent Base Scalar Normalization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentBaseScalarNormalization.Dolbeault

noncomputable section

/-! Homogeneous base-Cech monomials have exactly their canonical original scalar coefficient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {σ : Type}

attribute [local instance] MvPolynomial.gradedAlgebra

theorem coordinateBaseHomogeneousLaurent_single {q : ℕ}
    (a : Fin (q + 1) → ULift.{u} σ) (d : ℤ)
    (c : SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechFactor (SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R))) (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R)) q a)
    (e : SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a k).down)))
    (r : Γ(Spec (CommRingCat.of R), ⊤))
    (hc : SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := R) a d c =
      AddMonoidAlgebra.single (SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv (fun k => (a k).down) d e) r) :
    SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a c =
      AddMonoidAlgebra.single e ((Scheme.ΓSpecIso (CommRingCat.of R)).hom r) := by
  let L := SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) a
  let H := SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv (R := R) a d
  have hc' : c = L.symm (AddMonoidAlgebra.single e r) :=
    H.injective (hc.trans (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseHomogeneousLaurentLinearEquiv_basis_apply
      (R := R) a d e r).symm)
  have hL := (congrArg L hc').trans (L.apply_symm_apply (AddMonoidAlgebra.single e r))
  let C := AddMonoidAlgebra.mapRingEquiv
    (SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun k => (a k).down)))
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm
  change C (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a c) = AddMonoidAlgebra.single e r at hL
  have hC : C (AddMonoidAlgebra.single e ((Scheme.ΓSpecIso (CommRingCat.of R)).hom r)) =
      AddMonoidAlgebra.single e r := by
    rw [AddMonoidAlgebra.mapRingEquiv_single]
    exact congrArg (AddMonoidAlgebra.single e)
      (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of R)) r)
  exact C.injective (hL.trans hC.symm)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.LaurentBaseScalarNormalization.Dolbeault
