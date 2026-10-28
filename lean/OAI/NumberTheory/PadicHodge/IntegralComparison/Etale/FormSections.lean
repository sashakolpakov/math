import OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.FormSectionUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateFormBasis
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD

/-! # Form Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.FormSections.Integral

noncomputable section

/-! Exact sections of the original differential-form module sheaf on
affine étale-coordinate opens. The comparison is the original symbol
map to exterior Kähler differentials and commutes with restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionUnit.Intrinsic

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

local instance sectionModule (n : ℕ) (U : X.left.Opens) :
    Module (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n, U) :=
  inferInstanceAs (Module Γ(X.left, U) Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n, U))

variable (U : X.left.Opens) (hU : IsAffineOpen U)
  (σ : Type u) [LinearOrder σ] [Algebra (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U)]
  [IsScalarTower R (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U)]
  [Algebra.Etale (MvPolynomial σ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U)]

include hU σ in
theorem unit_bijective (n : ℕ) :
    Function.Bijective (Integral.FormSectionUnit.unit R X n U) := by
  let := AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OpenOrdinaryFormUnit.BaseAffineOpenOrdinaryFormUnit.forms R X U hU σ n
  exact Integral.FormSectionUnit.bijective R X n U

def unitIso (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) n ≃ₗ[IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U]
    Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n, U) :=
  LinearEquiv.ofBijective (Integral.FormSectionUnit.unit R X n U)
    (unit_bijective R X U hU σ n)

def exteriorIso (n : ℕ) : Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n, U) ≃ₗ[IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U]
    ⋀[IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U]^n (KaehlerDifferential R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U)) :=
  (unitIso R X U hU σ n).symm.trans
    (CoordinateFormBasis.exteriorEquiv R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) σ n)

theorem exteriorIso_unit (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) n) :
    exteriorIso R X U hU σ n (Integral.FormSectionUnit.unit R X n U ω) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) n ω := by
  change CoordinateFormBasis.exteriorEquiv R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) σ n
    ((unitIso R X U hU σ n).symm ((unitIso R X U hU σ n) ω)) = _
  rw [LinearEquiv.symm_apply_apply]
  exact LinearMap.congr_fun (CoordinateFormBasis.exteriorEquiv_eq R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) σ n) ω

theorem exteriorIso_symbol (n : ℕ) (a : IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (v : Fin n → IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) :
    exteriorIso R X U hU σ n
      (Integral.FormSectionUnit.unit R X n U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) a v)) =
      a • exteriorPower.ιMulti (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) n (fun i => KaehlerDifferential.D R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (v i)) := by
  rw [exteriorIso_unit, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.toExterior_symbol]
  rfl

theorem exteriorIso_chart_independent (τ : Type u) [LinearOrder τ]
    [Algebra (MvPolynomial τ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U)]
    [IsScalarTower R (MvPolynomial τ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U)]
    [Algebra.Etale (MvPolynomial τ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U)] (n : ℕ) :
    exteriorIso R X U hU σ n = exteriorIso R X U hU τ n := by
  ext s
  obtain ⟨ω, rfl⟩ := unit_bijective R X U hU σ n |>.surjective s
  rw [exteriorIso_unit, exteriorIso_unit]

variable (V : X.left.Opens) (hV : IsAffineOpen V)
  (τ : Type u) [LinearOrder τ] [Algebra (MvPolynomial τ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V)]
  [IsScalarTower R (MvPolynomial τ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V)]
  [Algebra.Etale (MvPolynomial τ R) (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V)]

theorem exteriorIso_restriction (i : V ⟶ U) (n : ℕ)
    (s : Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n, U)) :
    exteriorIso R X V hV τ n ((GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n).presheaf.map i.op s) =
      AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map i.op) n
        (exteriorIso R X U hU σ n s) := by
  obtain ⟨ω, rfl⟩ := unit_bijective R X U hU σ n |>.surjective s
  rw [Integral.FormSectionUnit.restriction, exteriorIso_unit, exteriorIso_unit]
  exact AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.toExterior_natural (R := R) (B := IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U) (C := IntrinsicDeRham.SectionUnit.Intrinsic.ring R X V)
    ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map i.op) n ω

theorem exteriorIso_symm_restriction (i : V ⟶ U) (n : ℕ)
    (ω : ⋀[IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U]^n (KaehlerDifferential R (IntrinsicDeRham.SectionUnit.Intrinsic.ring R X U))) :
    (GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R X n).presheaf.map i.op
      ((exteriorIso R X U hU σ n).symm ω) =
      (exteriorIso R X V hV τ n).symm
        (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map i.op) n ω) := by
  apply (exteriorIso R X V hV τ n).injective
  rw [exteriorIso_restriction R X U hU σ V hV τ, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.FormSections.Integral
