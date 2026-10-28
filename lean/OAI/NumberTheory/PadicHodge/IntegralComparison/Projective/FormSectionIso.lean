import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopFormMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionUnit
import Mathlib.RingTheory.Etale.Basic

/-! # Form Section Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FormSectionIso

noncomputable section

/-! Native projective differential symbols are precisely the actual
form-sheaf sections on each affine coordinate chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] {n : ℕ} (i : Fin (n + 1))
attribute [local instance] MvPolynomial.gradedAlgebra

def coordinateEquiv : IntrinsicOverlap.Intrinsic.ring R n (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i) ≃ₐ[R] MvPolynomial (ULift.{u} (Fin n)) R := by
  letI := ChartAlgebra.algebra (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  exact (ChartAlgebra.equiv (R := R) i).trans
    (MvPolynomial.renameEquiv R ((finSuccAboveEquiv i).symm.trans Equiv.ulift.symm))

theorem sectionUnit_bijective (d : ℕ) :
    Function.Bijective (Integral.FormSectionUnit.unit R (IntrinsicOverlap.Intrinsic.model R n) d (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i)) := by
  let C := IntrinsicOverlap.Intrinsic.ring R n (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  let P := MvPolynomial (ULift.{u} (Fin n)) R
  let e : C ≃ₐ[R] P := coordinateEquiv i
  let : Algebra P C := Polynomial.CoordinateDifferentials.polynomialAlgebra e
  let : IsScalarTower R P C := Polynomial.CoordinateDifferentials.tower e
  let e' : P ≃ₐ[P] C := { e.symm.toRingEquiv with commutes' := fun _ => rfl }
  let : Algebra.Etale P C := Algebra.Etale.of_equiv e'
  have hIso : IsIso ((toSheafify (Opens.grothendieckTopology (IntrinsicOverlap.Intrinsic.space R n))
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R (IntrinsicOverlap.Intrinsic.model R n) d)).app (op (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i))) :=
    AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenOrdinaryFormUnit.BaseAffineOpenOrdinaryFormUnit.forms R (IntrinsicOverlap.Intrinsic.model R n) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i)
      (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i) (ULift.{u} (Fin n)) d
  exact @Integral.FormSectionUnit.bijective R _ (IntrinsicOverlap.Intrinsic.model R n) d (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i) hIso

local instance sectionModule (d : ℕ) (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) :
    Module (IntrinsicOverlap.Intrinsic.ring R n U) Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R (IntrinsicOverlap.Intrinsic.model R n) d, U) :=
  inferInstanceAs (Module Γ(IntrinsicOverlap.Intrinsic.space R n, U) Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R (IntrinsicOverlap.Intrinsic.model R n) d, U))

def sectionUnitIso (d : ℕ) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (IntrinsicOverlap.Intrinsic.ring R n (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i)) d ≃ₗ[IntrinsicOverlap.Intrinsic.ring R n (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i)]
      Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R (IntrinsicOverlap.Intrinsic.model R n) d, AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i) :=
  LinearEquiv.ofBijective (Integral.FormSectionUnit.unit R (IntrinsicOverlap.Intrinsic.model R n) d (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i))
    (sectionUnit_bijective i d)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FormSectionIso
