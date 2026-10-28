import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopFormIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.FormSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.LinearHom
import OAI.NumberTheory.PadicHodge.IntegralComparison.TopExteriorBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionRestriction

/-! # Ambient Adjunction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AmbientAdjunction

noncomputable section

/-! The actual projective dualizing line gives ambient top differentials
on every affine subopen of a coordinate chart, including after passage
to an arbitrary quotient of its section ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.MvPolynomial
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

local instance sectionAlgebra (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) : Algebra R Γ(IntrinsicOverlap.Intrinsic.space R n, U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (IntrinsicOverlap.Intrinsic.model R n) U

variable (i : Fin (n + 1)) (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)
  (h : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)

abbrev restriction := (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R (IntrinsicOverlap.Intrinsic.model R n)).map (homOfLE h).op

@[instance_reducible]
def polynomialAlgebra : Algebra (MvPolynomial (ULift.{u} (Fin n)) R) (IntrinsicOverlap.Intrinsic.ring R n U) :=
  ((restriction i U h).hom.comp
    (FormSectionIso.coordinateEquiv i).symm.toAlgHom).toRingHom.toAlgebra

theorem tower : letI := polynomialAlgebra i U h
    IsScalarTower R (MvPolynomial (ULift.{u} (Fin n)) R) (IntrinsicOverlap.Intrinsic.ring R n U) := by
  let := polynomialAlgebra i U h
  exact IsScalarTower.of_algebraMap_eq (fun r =>
    (((restriction i U h).hom.comp
      (FormSectionIso.coordinateEquiv i).symm.toAlgHom).commutes r).symm)

include hU in
theorem etale : letI := polynomialAlgebra i U h
    Algebra.Etale (MvPolynomial (ULift.{u} (Fin n)) R) (IntrinsicOverlap.Intrinsic.ring R n U) := by
  let C := IntrinsicOverlap.Intrinsic.ring R n (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
  let P := MvPolynomial (ULift.{u} (Fin n)) R
  let e : C ≃ₐ[R] P := FormSectionIso.coordinateEquiv i
  let : Algebra P C := Polynomial.CoordinateDifferentials.polynomialAlgebra e
  let e' : P ≃ₐ[P] C := { e.symm.toRingEquiv with commutes' := fun _ => rfl }
  have h₁ : e.symm.toRingHom.Etale :=
    RingHom.etale_algebraMap.mpr (Algebra.Etale.of_equiv e')
  have h₂ : (restriction i U h).hom.toRingHom.Etale := by
    let := IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionAlgebra R (IntrinsicOverlap.Intrinsic.model R n) (homOfLE h)
    exact RingHom.etale_algebraMap.mpr
      (IntrinsicDeRham.SectionRestriction.IntrinsicUnit.restrictionEtale R (IntrinsicOverlap.Intrinsic.model R n) (homOfLE h)
        (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i) hU)
  let := polynomialAlgebra i U h
  exact RingHom.etale_algebraMap.mp (RingHom.Etale.stableUnderComposition _ _ h₁ h₂)

def formExterior (d : ℕ) :
    Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R (IntrinsicOverlap.Intrinsic.model R n) d, U) ≃ₗ[Γ(IntrinsicOverlap.Intrinsic.space R n, U)]
      ⋀[Γ(IntrinsicOverlap.Intrinsic.space R n, U)]^d Ω[Γ(IntrinsicOverlap.Intrinsic.space R n, U)⁄R] := by
  letI := polynomialAlgebra i U h
  letI := tower i U h
  letI := etale i U hU h
  exact IntegralComparison.Etale.FormSections.Integral.exteriorIso R (IntrinsicOverlap.Intrinsic.model R n) U hU (ULift.{u} (Fin n)) d

theorem formExterior_unit (d : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (IntrinsicOverlap.Intrinsic.ring R n U) d) :
    formExterior i U hU h d (Integral.FormSectionUnit.unit R (IntrinsicOverlap.Intrinsic.model R n) d U ω) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior R (IntrinsicOverlap.Intrinsic.ring R n U) d ω := by
  let := polynomialAlgebra i U h
  let := tower i U h
  let := etale i U hU h
  exact IntegralComparison.Etale.FormSections.Integral.exteriorIso_unit R (IntrinsicOverlap.Intrinsic.model R n) U hU
    (ULift.{u} (Fin n)) d ω

def lineExterior (j : Fin (n + 1)) :
    Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1), U) ≃ₗ[Γ(IntrinsicOverlap.Intrinsic.space R n, U)]
      ⋀[Γ(IntrinsicOverlap.Intrinsic.space R n, U)]^n Ω[Γ(IntrinsicOverlap.Intrinsic.space R n, U)⁄R] :=
  ((Affine.ModuleExactSections.sections U).mapIso
    (TopFormIso.iso (R := R) j)).toLinearEquiv.trans (formExterior i U hU h n)

def chartLineExterior (j : Fin (n + 1)) :
    (AffineOpen.InternalHom.sections U hU).obj
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)) ≃ₗ[Γ(IntrinsicOverlap.Intrinsic.space R n, U)]
        ⋀[Γ(IntrinsicOverlap.Intrinsic.space R n, U)]^n Ω[Γ(IntrinsicOverlap.Intrinsic.space R n, U)⁄R] :=
  ((AffineOpen.LinearHom.sectionsIso U hU).symm.app _).toLinearEquiv.trans
    (lineExterior i U hU h j)

def differentialBasis : Module.Basis (Fin n) Γ(IntrinsicOverlap.Intrinsic.space R n, U) Ω[Γ(IntrinsicOverlap.Intrinsic.space R n, U)⁄R] :=
  (IntrinsicOverlap.Intrinsic.restrictedBasis i (homOfLE h) hU).reindex Equiv.ulift

def ambientIso (j : Fin (n + 1)) (I : Ideal Γ(IntrinsicOverlap.Intrinsic.space R n, U)) :
    (Γ(IntrinsicOverlap.Intrinsic.space R n, U) ⧸ I) ⊗[Γ(IntrinsicOverlap.Intrinsic.space R n, U)]
      (AffineOpen.InternalHom.sections U hU).obj
        (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)) ≃ₗ[Γ(IntrinsicOverlap.Intrinsic.space R n, U) ⧸ I]
      ⋀[Γ(IntrinsicOverlap.Intrinsic.space R n, U) ⧸ I]^n
        ((Γ(IntrinsicOverlap.Intrinsic.space R n, U) ⧸ I) ⊗[Γ(IntrinsicOverlap.Intrinsic.space R n, U)] Ω[Γ(IntrinsicOverlap.Intrinsic.space R n, U)⁄R]) :=
  ((chartLineExterior i U hU h j).baseChange Γ(IntrinsicOverlap.Intrinsic.space R n, U) (Γ(IntrinsicOverlap.Intrinsic.space R n, U) ⧸ I) _ _).trans
    (TopExteriorBaseChange.equiv (Γ(IntrinsicOverlap.Intrinsic.space R n, U) ⧸ I) (differentialBasis i U hU h))

attribute [local irreducible] chartLineExterior differentialBasis

theorem ambientIso_tmul (j : Fin (n + 1)) (I : Ideal Γ(IntrinsicOverlap.Intrinsic.space R n, U))
    (a : Γ(IntrinsicOverlap.Intrinsic.space R n, U) ⧸ I)
    (s : (AffineOpen.InternalHom.sections U hU).obj
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1))) :
    ambientIso i U hU h j I (a ⊗ₜ[Γ(IntrinsicOverlap.Intrinsic.space R n, U)] s) =
      GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap Γ(IntrinsicOverlap.Intrinsic.space R n, U) (Γ(IntrinsicOverlap.Intrinsic.space R n, U) ⧸ I)
        Ω[Γ(IntrinsicOverlap.Intrinsic.space R n, U)⁄R] n
          (a ⊗ₜ[Γ(IntrinsicOverlap.Intrinsic.space R n, U)] chartLineExterior i U hU h j s) := by
  exact TopExteriorBaseChange.composite_tmul (Γ(IntrinsicOverlap.Intrinsic.space R n, U) ⧸ I)
    (differentialBasis i U hU h) (chartLineExterior i U hU h j) a s

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AmbientAdjunction
