import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FormSectionIso
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OrdinaryFormCoherence
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormsOpenRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.SectionBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.ModuleGenerators

/-! # Form Quasicoherence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FormQuasicoherence

noncomputable section

/-! The original differential-form module sheaves are quasicoherent on
the actual projective coordinate charts, in every degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FormSectionIso

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] {n : ℕ} (i : Fin (n + 1))
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev chartModel : Over (Spec (CommRingCat.of R)) :=
  AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.SectionTowers.BaseAffineSectionTowers.affineScheme R (IntrinsicOverlap.Intrinsic.ring R n (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i))

theorem chart_over : (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen (R := R) i).fromSpec ≫ (IntrinsicOverlap.Intrinsic.model R n).hom =
    (chartModel i).hom := AffineOpen.SectionBase.overBase R (IntrinsicOverlap.Intrinsic.model R n)
      (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i)

def chartIso (d : ℕ) : GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R (chartModel i) d ≅
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R (IntrinsicOverlap.Intrinsic.model R n) d).restrict (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i).fromSpec := by
  letI : IsOpenImmersion (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen (R := R) i).fromSpec :=
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i).isOpenImmersion_fromSpec
  exact GeometricComparison.Integral.FormsOpenRestriction.IntegralFormsOpenRestriction.iso (chartModel i) (IntrinsicOverlap.Intrinsic.model R n)
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i).fromSpec (chart_over i) d

theorem chart_quasicoherent (d : ℕ) :
    ((GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R (IntrinsicOverlap.Intrinsic.model R n) d).restrict (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i).fromSpec).IsQuasicoherent := by
  let C := IntrinsicOverlap.Intrinsic.ring R n (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  let P := MvPolynomial (ULift.{u} (Fin n)) R
  let e : C ≃ₐ[R] P := FormSectionIso.coordinateEquiv i
  let : Algebra P C := Polynomial.CoordinateDifferentials.polynomialAlgebra e
  let : IsScalarTower R P C := Polynomial.CoordinateDifferentials.tower e
  let : Algebra.FormallyEtale P C := Polynomial.CoordinateDifferentials.formallyEtale e
  have h : (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R (chartModel i) d).IsQuasicoherent := by
    exact AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OrdinaryFormCoherence.BaseAffineOrdinaryFormCoherence.quasicoherent R C (ULift.{u} (Fin n)) d
  exact (AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent _).prop_of_iso (chartIso i d) h

theorem open_quasicoherent (d : ℕ) :
    ((GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R (IntrinsicOverlap.Intrinsic.model R n) d).restrict (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i).ι).IsQuasicoherent := by
  let := chart_quasicoherent (R := R) i d
  exact AffineOpen.ModuleGenerators.quasicoherent
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R (IntrinsicOverlap.Intrinsic.model R n) d) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i)

theorem over_quasicoherent (d : ℕ) :
    ((GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R (IntrinsicOverlap.Intrinsic.model R n) d).over (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i)).IsQuasicoherent := by
  let : IsAffine (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).toScheme := AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i
  let := open_quasicoherent (R := R) i d
  exact AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_over_of_restrict_of_isAffineOpen
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R (IntrinsicOverlap.Intrinsic.model R n) d) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i)

omit i in
theorem quasicoherent (d : ℕ) : (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R (IntrinsicOverlap.Intrinsic.model R n) d).IsQuasicoherent := by
  let U : ULift.{u} (Fin (n + 1)) → (IntrinsicOverlap.Intrinsic.space R n).Opens := fun i => AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen i.down
  have hU : (Opens.grothendieckTopology (IntrinsicOverlap.Intrinsic.space R n)).CoversTop U := by
    rw [Opens.coversTop_iff, TopologicalSpace.IsOpenCover]
    simpa only [U, iSup_ulift] using (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top (R := R) (σ := Fin (n + 1)))
  exact @SheafOfModules.IsQuasicoherent.of_coversTop _ _ _ _ _ _ _ _
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R (IntrinsicOverlap.Intrinsic.model R n) d) _ U hU
    (fun i => over_quasicoherent (R := R) i.down d)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.FormQuasicoherence
