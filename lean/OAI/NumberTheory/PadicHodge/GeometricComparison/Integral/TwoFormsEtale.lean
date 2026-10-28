import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ExteriorPowerBaseChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExteriorPowerCongr
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.TwoForms
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.LowDegreeLocalization

/-! # Two Forms Etale -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.TwoFormsEtale.IntegralTwoFormsEtale

noncomputable section

/-! Integral two-forms commute with flat formally étale coordinate extension, including localization at the prime two. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation
open scoped TensorProduct

universe u

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Module.Flat A B] [Algebra.FormallyEtale A B]

def equiv : B ⊗[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 2 ≃ₗ[B] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B 2 :=
  ((TwoForms.IntegralTwoForms.equiv R A).baseChange A B _ _).trans
    ((ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerEquiv A B (KaehlerDifferential R A) 2).trans
      ((ExteriorPowerCongr.ExteriorBaseChange.powerCongr 2
        (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B)).trans
          (TwoForms.IntegralTwoForms.equiv R B).symm))

theorem equiv_symbol (b : B) (a : A) (v : Fin 2 → A) :
    equiv R A B (b ⊗ₜ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B (b * algebraMap A B a) (fun i => algebraMap A B (v i)) := by
  apply (TwoForms.IntegralTwoForms.equiv R B).injective
  simp only [equiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.baseChange_tmul, TwoForms.IntegralTwoForms.equiv_symbol, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.exteriorSymbol,
    TensorProduct.tmul_smul]
  refine (congrArg (ExteriorPowerCongr.ExteriorBaseChange.powerCongr 2
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B))
    (ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerEquiv_tmul_ιMulti A B (KaehlerDifferential R A) 2
      (a • b) (fun i => KaehlerDifferential.D R A (v i)))).trans ?_
  rw [map_smul, ExteriorPowerCongr.ExteriorBaseChange.powerCongr_ιMulti]
  have h : (fun i => KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B
      (1 ⊗ₜ[A] KaehlerDifferential.D R A (v i))) =
      fun i => KaehlerDifferential.D R B (algebraMap A B (v i)) := by
    funext i
    exact (congrArg (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B)
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap R A B (v i))).symm.trans
        ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B).apply_symm_apply _)
  rw [h, Algebra.smul_def, mul_comm]

theorem equiv_one_tmul (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 2) :
    equiv R A B (1 ⊗ₜ[A] ω) = Forms.CoordinateLinearity.FormsBaseChange.coordinateFormMap R A B 2 ω := by
  obtain ⟨x, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A 2).mkQ_surjective ω
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  | single v a =>
    change equiv R A B (1 ⊗ₜ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      Forms.CoordinateLinearity.FormsBaseChange.coordinateFormMap R A B 2 (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)
    rw [equiv_symbol, one_mul, Forms.CoordinateLinearity.FormsBaseChange.coordinateFormMap_symbol]

theorem isBaseChange : IsBaseChange B (Forms.CoordinateLinearity.FormsBaseChange.coordinateFormMap R A B 2) := by
  have h := (TensorProduct.isBaseChange A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 2) B).comp (IsBaseChange.ofEquiv (equiv R A B))
  have he : ((equiv R A B).toLinearMap.restrictScalars A).comp
      (TensorProduct.mk A B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 2) 1) = Forms.CoordinateLinearity.FormsBaseChange.coordinateFormMap R A B 2 :=
    LinearMap.ext (equiv_one_tmul R A B)
  exact he ▸ h

omit [Module.Flat A B] [Algebra.FormallyEtale A B] in
theorem isLocalized (T : Submonoid A) [IsLocalization T B] :
    IsLocalizedModule T (Forms.CoordinateLinearity.FormsBaseChange.coordinateFormMap R A B 2) := by
  let : Module.Flat A B := IsLocalization.flat B T
  let : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization T
  exact (isLocalizedModule_iff_isBaseChange T B _).mpr (IntegralTwoFormsEtale.isBaseChange R A B)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.TwoFormsEtale.IntegralTwoFormsEtale
