import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.AdditiveIsoNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.CohomologyLinearity
import OAI.NumberTheory.PadicHodge.GeometricComparison.ProEtalePullback
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius

/-! # Cohomology Iso Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.CohomologyIsoNaturality.RationalProEtaleCoefficients

noncomputable section

/-! The actual integral-to-rational cohomology inclusion commutes with scheme-isomorphism transport. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology OAI.NumberTheory.PadicHodge.IntegralComparison.ProEtale OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius

variable (ℓ : ℕ) [Fact ℓ.Prime] {X Y : Scheme.{0}} (e : X ≅ Y)

theorem integralInclusion_iso :
    (IntegralComparison.ProEtale.proEtaleSheafCongr Ab.{1} e).functor.map (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X) = ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ Y := rfl

theorem cohomologyEquiv_transport (n : ℕ) (x : IntegralComparison.Cohomology.RationalEllAdicCohomology ℓ X n) :
    ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyEquiv ℓ Y n (IntegralComparison.Etale.Frobenius.cohomologyTransport ℓ e n x) =
      (Ext.mk₀ ((IntegralComparison.ProEtale.proEtaleSheafCongr_constant Ab.{1} e).inv.app
          (AddCommGrpCat.of (ULift.{1} ℤ)))).comp
        ((ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyEquiv ℓ X n x).mapExactFunctor (IntegralComparison.ProEtale.proEtaleSheafCongr Ab.{1} e).functor) (zero_add n) := by
  let y : Ext (AdditiveSheaf.AdditiveSheafCohomology.fieldConstant (IntegralComparison.Cohomology.Coeff.{0} ℓ) (Scheme.ProEt.topology X))
      (IntegralComparison.Cohomology.rationalCoefficientSheaf ℓ X) n := x
  have h := Cohomology.AdditiveIsoNaturality.AdditiveSheafCohomology.equiv_iso (IntegralComparison.Cohomology.Coeff.{0} ℓ) e (IntegralComparison.Cohomology.rationalCoefficientSheaf ℓ X) n y
  change ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyEquiv ℓ Y n
    (((Ext.mk₀ ((IntegralComparison.Etale.Frobenius.constantUnitTransport ℓ e).inv)).comp
      (y.mapExactFunctor (IntegralComparison.ProEtale.proEtaleSheafCongr (ModuleCat.{1} (IntegralComparison.Cohomology.Coeff.{0} ℓ)) e).functor)
        (zero_add n)).comp (Ext.mk₀ (𝟙 _)) (add_zero n)) = _
  rw [Ext.comp_mk₀_id]
  exact h

theorem additiveInclusion_transport (n : ℕ) (x : X.EllAdicCohomology ℓ n) :
    Sheaf.H.map (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ Y) n (ProEtalePullback.ProEtaleIsoCohomology.transportPullback e.symm ℓ n x) =
      (Ext.mk₀ ((IntegralComparison.ProEtale.proEtaleSheafCongr_constant Ab.{1} e).inv.app
          (AddCommGrpCat.of (ULift.{1} ℤ)))).comp
        ((Sheaf.H.map (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X) n x).mapExactFunctor
          (IntegralComparison.ProEtale.proEtaleSheafCongr Ab.{1} e).functor) (zero_add n) := by
  let y : (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ X).H n := x
  change ((Ext.mk₀ ((IntegralComparison.ProEtale.proEtaleSheafCongr_constant Ab.{1} e).inv.app
        (AddCommGrpCat.of (ULift.{1} ℤ)))).comp
      (y.mapExactFunctor (IntegralComparison.ProEtale.proEtaleSheafCongr Ab.{1} e).functor) (zero_add n)).comp
        (Ext.mk₀ (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ Y)) (add_zero n) = _
  change _ = (Ext.mk₀ ((IntegralComparison.ProEtale.proEtaleSheafCongr_constant Ab.{1} e).inv.app
      (AddCommGrpCat.of (ULift.{1} ℤ)))).comp
    ((y.comp (Ext.mk₀ (ProEtaleCoefficients.RationalProEtaleCoefficients.integralInclusion ℓ X)) (add_zero n)).mapExactFunctor
      (IntegralComparison.ProEtale.proEtaleSheafCongr Ab.{1} e).functor) (zero_add n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, integralInclusion_iso,
    Ext.comp_assoc_of_third_deg_zero]
  rfl

theorem cohomologyInclusion_transport (n : ℕ) (x : X.EllAdicCohomology ℓ n) :
    ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyInclusion ℓ Y n (ProEtalePullback.ProEtaleIsoCohomology.transportPullback e.symm ℓ n x) =
      IntegralComparison.Etale.Frobenius.cohomologyTransport ℓ e n (ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyInclusion ℓ X n x) := by
  apply (ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyEquiv ℓ Y n).injective
  rw [CohomologyLinearity.RationalProEtaleCoefficients.cohomologyEquiv_inclusion, cohomologyEquiv_transport, CohomologyLinearity.RationalProEtaleCoefficients.cohomologyEquiv_inclusion]
  exact additiveInclusion_transport ℓ e n x

theorem cohomologyInclusion_pullback (n : ℕ) (x : Y.EllAdicCohomology ℓ n) :
    ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyInclusion ℓ X n (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.integralEllAdicPullback ℓ e.hom n x) =
      IntegralComparison.Etale.Frobenius.cohomologyPullback ℓ e n (ProEtaleCoefficients.RationalProEtaleCoefficients.cohomologyInclusion ℓ Y n x) := by
  rw [ProEtalePullback.ProEtaleIsoCohomology.integral_pullback]
  exact cohomologyInclusion_transport ℓ e.symm n x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Rational.CohomologyIsoNaturality.RationalProEtaleCoefficients
