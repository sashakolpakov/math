import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionRestriction

/-! # Etale Coordinate Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.EtaleCoordinateRestriction

noncomputable section

/-! Polynomial étale coordinates restrict to any actual affine subopen,
with the original base algebra and literal restriction map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionRestriction.IntrinsicUnit
universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {U V : X.left.Opens} (i : V ⟶ U)
  (σ : Type u) [Algebra (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U)]
  [IsScalarTower R (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U)]

omit [IsScalarTower R (MvPolynomial σ R) ↑(IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U)] in
@[instance_reducible]
def algebra : Algebra (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V) :=
  (((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map i.op).hom.toRingHom.comp
    (algebraMap (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U))).toAlgebra

theorem tower : letI := algebra R X i σ
    IsScalarTower R (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V) := by
  let := algebra R X i σ
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change algebraMap R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V) r =
    ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map i.op).hom
      (algebraMap (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (algebraMap R (MvPolynomial σ R) r))
  rw [← IsScalarTower.algebraMap_apply]
  exact (((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map i.op).hom.commutes r).symm

variable [Algebra.Etale (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U)]

omit [IsScalarTower R (MvPolynomial σ R) ↑(IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U)] in
theorem etale (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI := algebra R X i σ
    Algebra.Etale (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V) := by
  let := IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionAlgebra R X i
  let := algebra R X i σ
  let : IsScalarTower (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let := IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionEtale R X i hU hV
  exact Algebra.Etale.comp (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.EtaleCoordinateRestriction
