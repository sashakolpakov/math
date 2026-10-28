import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AmbientAdjunction

/-! # Ambient Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AmbientNormalization.Adjunction

noncomputable section

/-! The ambient top-form comparison is independent of the projective
coordinate chart and uses the canonical restriction of exterior forms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.MvPolynomial
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

attribute [local instance] AmbientAdjunction.sectionAlgebra

variable (i : Fin (n + 1)) (U : (IntrinsicOverlap.Intrinsic.space R n).Opens) (hU : IsAffineOpen U)
  (h : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)

theorem formExterior_independent_chart (k : Fin (n + 1))
    (hk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k) (d : ℕ) :
    AmbientAdjunction.formExterior i U hU h d = AmbientAdjunction.formExterior k U hU hk d := by
  let := AmbientAdjunction.polynomialAlgebra i U h
  let := AmbientAdjunction.tower i U h
  let := AmbientAdjunction.etale i U hU h
  ext s
  obtain ⟨ω, rfl⟩ := Etale.FormSections.Integral.unit_bijective R (IntrinsicOverlap.Intrinsic.model R n) U hU
    (ULift.{u} (Fin n)) d |>.surjective s
  rw [AmbientAdjunction.formExterior_unit, AmbientAdjunction.formExterior_unit]

theorem lineExterior_independent_chart (k : Fin (n + 1))
    (hk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k) (j : Fin (n + 1)) :
    AmbientAdjunction.lineExterior i U hU h j = AmbientAdjunction.lineExterior k U hU hk j := by
  rw [AmbientAdjunction.lineExterior, AmbientAdjunction.lineExterior, formExterior_independent_chart i U hU h k hk]

theorem chartLineExterior_independent_chart (k : Fin (n + 1))
    (hk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k) (j : Fin (n + 1)) :
    AmbientAdjunction.chartLineExterior i U hU h j = AmbientAdjunction.chartLineExterior k U hU hk j := by
  rw [AmbientAdjunction.chartLineExterior, AmbientAdjunction.chartLineExterior, lineExterior_independent_chart i U hU h k hk]

theorem ambientIso_independent_chart (k : Fin (n + 1))
    (hk : U ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k) (j : Fin (n + 1)) (I : Ideal Γ(IntrinsicOverlap.Intrinsic.space R n, U)) :
    AmbientAdjunction.ambientIso i U hU h j I = AmbientAdjunction.ambientIso k U hU hk j I := by
  unfold AmbientAdjunction.ambientIso
  exact congrArg₂ LinearEquiv.trans
    (congrArg (fun e => e.baseChange Γ(IntrinsicOverlap.Intrinsic.space R n, U) (Γ(IntrinsicOverlap.Intrinsic.space R n, U) ⧸ I) _ _)
      (chartLineExterior_independent_chart i U hU h k hk j))
    (TopExteriorBaseChange.independent_basis (Γ(IntrinsicOverlap.Intrinsic.space R n, U) ⧸ I)
      (AmbientAdjunction.differentialBasis i U hU h) (AmbientAdjunction.differentialBasis k U hU hk))

variable (k : Fin (n + 1)) (V : (IntrinsicOverlap.Intrinsic.space R n).Opens) (hV : IsAffineOpen V)
  (hk : V ≤ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)

theorem formExterior_restriction (a : V ⟶ U) (d : ℕ)
    (s : Γ(GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R (IntrinsicOverlap.Intrinsic.model R n) d, U)) :
    AmbientAdjunction.formExterior k V hV hk d ((GeometricComparison.Integral.FormsModules.IntegralFormsModules.sheaf R (IntrinsicOverlap.Intrinsic.model R n) d).presheaf.map a.op s) =
      AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R (IntrinsicOverlap.Intrinsic.model R n)).map a.op) d
        (AmbientAdjunction.formExterior i U hU h d s) := by
  let := AmbientAdjunction.polynomialAlgebra i U h
  let := AmbientAdjunction.tower i U h
  let := AmbientAdjunction.etale i U hU h
  let := AmbientAdjunction.polynomialAlgebra k V hk
  let := AmbientAdjunction.tower k V hk
  let := AmbientAdjunction.etale k V hV hk
  exact Etale.FormSections.Integral.exteriorIso_restriction R (IntrinsicOverlap.Intrinsic.model R n) U hU
    (ULift.{u} (Fin n)) V hV (ULift.{u} (Fin n)) a d s

theorem lineExterior_restriction (a : V ⟶ U) (j : Fin (n + 1))
    (s : Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1), U)) :
    AmbientAdjunction.lineExterior k V hV hk j
      ((AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)).presheaf.map a.op s) =
      AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R (IntrinsicOverlap.Intrinsic.model R n)).map a.op) n
        (AmbientAdjunction.lineExterior i U hU h j s) := by
  change AmbientAdjunction.formExterior k V hV hk n
    ((TopFormIso.iso (R := R) j).hom.val.app (op V)
      ((AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)).presheaf.map a.op s)) = _
  exact (congrArg (AmbientAdjunction.formExterior k V hV hk n)
    (PresheafOfModules.naturality_apply (TopFormIso.iso (R := R) j).hom.val a.op s)).trans
      (formExterior_restriction i U hU h k V hV hk a n _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AmbientNormalization.Adjunction
