import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionRestriction

/-! # Section Coordinates Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.SectionCoordinatesRestriction

noncomputable section

/-! Affine restrictions inherit the original polynomial étale
coordinates through the actual map on sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionRestriction.IntrinsicUnit

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {U V : X.left.Opens} (i : V ⟶ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
  (σ : Type u) [Algebra (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U)]

@[instance_reducible]
def polynomialAlgebra : Algebra (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V) :=
  (((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map i.op).hom.toRingHom.comp
    (algebraMap (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U))).toAlgebra

variable [IsScalarTower R (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U)]

theorem tower : letI := polynomialAlgebra R X i σ
    IsScalarTower R (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V) := by
  let := polynomialAlgebra R X i σ
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change algebraMap R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V) r =
    ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map i.op).hom
      (algebraMap (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (algebraMap R (MvPolynomial σ R) r))
  rw [← IsScalarTower.algebraMap_apply]
  exact (((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map i.op).hom.commutes r).symm

variable [Algebra.Etale (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U)]

include hU hV in
omit [IsScalarTower R (MvPolynomial σ R) ↑(IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U)] in
theorem etale : letI := polynomialAlgebra R X i σ
    Algebra.Etale (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V) := by
  let := IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionAlgebra R X i
  let := IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionEtale R X i hU hV
  let := polynomialAlgebra R X i σ
  apply RingHom.etale_algebraMap.mp
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.etale_algebraMap.mpr (inferInstanceAs (Algebra.Etale (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U))))
    (RingHom.etale_algebraMap.mpr (inferInstanceAs (Algebra.Etale (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.SectionCoordinatesRestriction
