import OAI.NumberTheory.PadicHodge.GeometricComparison.AdditiveSheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback

/-! # Pro Etale Coefficients -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.ProEtaleCoefficients.RationalProEtaleCoefficients

noncomputable section

/-! The original rational pro-étale cohomology is compared with its actual additive coefficient sheaf, and the integral coefficient inclusion is constructed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology OAI.AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction

variable (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{0})

instance coefficientCharZero : CharZero (IntegralComparison.Cohomology.Coeff.{0} ℓ) :=
  charZero_of_injective_ringHom
    (f := (ULift.ringEquiv.symm : ℚ_[ℓ] ≃+* IntegralComparison.Cohomology.Coeff.{0} ℓ).toRingHom)
    (ULift.ringEquiv.symm : ℚ_[ℓ] ≃+* IntegralComparison.Cohomology.Coeff.{0} ℓ).injective

instance integerHasExt : HasExt.{1} (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{1} ℤ)) :=
  hasExt_of_enoughInjectives _

abbrev additiveSheaf : Sheaf (Scheme.ProEt.topology X) Ab.{1} :=
  AdditiveSheaf.AdditiveSheafCohomology.underlyingSheaf (IntegralComparison.Cohomology.Coeff.{0} ℓ) (Scheme.ProEt.topology X)
    (IntegralComparison.Cohomology.rationalCoefficientSheaf ℓ X)

def cohomologyEquiv (n : ℕ) : IntegralComparison.Cohomology.RationalEllAdicCohomology ℓ X n ≃+ (additiveSheaf ℓ X).H n :=
  AdditiveSheaf.AdditiveSheafCohomology.equiv (IntegralComparison.Cohomology.Coeff.{0} ℓ) (Scheme.ProEt.topology X)
    (IntegralComparison.Cohomology.rationalCoefficientSheaf ℓ X) n

def coefficientInclusion (T : Type*) [TopologicalSpace T] :
    ULift.{1} C(T, ℤ_[ℓ]) →+ C(T, IntegralComparison.Cohomology.Coeff.{0} ℓ) where
    toFun := fun s => ⟨fun x => ULift.up (s.down x : ℚ_[ℓ]),
      continuous_uliftUp.comp (continuous_subtype_val.comp s.down.continuous)⟩
    map_zero' := by ext x; rfl
    map_add' := by intro s t; ext x; rfl

def integralInclusion : AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X ⟶ additiveSheaf ℓ X where
  hom.app U := AddCommGrpCat.ofHom (coefficientInclusion ℓ U.unop.left)
  hom.naturality := by
    intro U V f
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    change (coefficientInclusion ℓ V.unop.left _ : C(V.unop.left, IntegralComparison.Cohomology.Coeff.{0} ℓ)) = _
    ext x
    rfl

def cohomologyInclusion (n : ℕ) : X.EllAdicCohomology ℓ n →+ IntegralComparison.Cohomology.RationalEllAdicCohomology ℓ X n :=
  (cohomologyEquiv ℓ X n).symm.toAddMonoidHom.comp (Sheaf.H.map (integralInclusion ℓ X) n)

def scalar (a : ℚ_[ℓ]) : additiveSheaf ℓ X ⟶ additiveSheaf ℓ X :=
  (IntegerSheaf.IntegerSheafEquivalence.forgetSheaf (Scheme.ProEt.topology X)).map
    ((SheafCoefficientCo.SheafCoefficientAdjunction.restrictSheaf (IntegralComparison.Cohomology.Coeff.{0} ℓ) (Scheme.ProEt.topology X)).map
      ((ULift.up a : IntegralComparison.Cohomology.Coeff.{0} ℓ) • 𝟙 (IntegralComparison.Cohomology.rationalCoefficientSheaf ℓ X)))

theorem cohomologyEquiv_smul (n : ℕ) (a : ℚ_[ℓ]) (x : IntegralComparison.Cohomology.RationalEllAdicCohomology ℓ X n) :
    cohomologyEquiv ℓ X n (a • x) = Sheaf.H.map (scalar ℓ X a) n (cohomologyEquiv ℓ X n x) := by
  let y : Ext (AdditiveSheaf.AdditiveSheafCohomology.fieldConstant (IntegralComparison.Cohomology.Coeff.{0} ℓ) (Scheme.ProEt.topology X))
      (IntegralComparison.Cohomology.rationalCoefficientSheaf ℓ X) n := x
  have h := AdditiveSheaf.AdditiveSheafCohomology.naturality (IntegralComparison.Cohomology.Coeff.{0} ℓ) (Scheme.ProEt.topology X)
    ((ULift.up a : IntegralComparison.Cohomology.Coeff.{0} ℓ) • 𝟙 (IntegralComparison.Cohomology.rationalCoefficientSheaf ℓ X)) n y
  rw [← Ext.smul_eq_comp_mk₀] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.ProEtaleCoefficients.RationalProEtaleCoefficients
