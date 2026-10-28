import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ExteriorPowerBaseChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExteriorPowerCongr
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.TwoForms
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.LowDegreeBaseChange
import Mathlib.RingTheory.Flat.Stability

/-! # Two Forms Base Change -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.TwoFormsBaseChange.IntegralTwoFormsBaseChange

noncomputable section

/-! Flat affine coefficient extension preserves native integral two-forms and the differential from one-forms. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation
open scoped TensorProduct

universe u

variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B] [Module.Flat R S]

include R S in
theorem affineFlat : Module.Flat A B := by
  let : Algebra.IsPushout R A S B := Algebra.IsPushout.symm inferInstance
  exact Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv R A S B).symm.toLinearEquiv

def tensorEquiv : B ⊗[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 2 ≃ₗ[B] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S B 2 := by
  let : Module.Flat A B := affineFlat R S A B
  exact ((TwoForms.IntegralTwoForms.equiv R A).baseChange A B _ _).trans
    ((ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerEquiv A B (KaehlerDifferential R A) 2).trans
      ((ExteriorPowerCongr.ExteriorBaseChange.powerCongr 2 (KaehlerDifferential.tensorKaehlerEquiv R S A B)).trans
        (TwoForms.IntegralTwoForms.equiv S B).symm))

theorem tensorEquiv_symbol (b : B) (a : A) (v : Fin 2 → A) :
    tensorEquiv R S A B (b ⊗ₜ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S B (b * algebraMap A B a) (fun i => algebraMap A B (v i)) := by
  let : Module.Flat A B := affineFlat R S A B
  apply (TwoForms.IntegralTwoForms.equiv S B).injective
  simp only [tensorEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.baseChange_tmul, TwoForms.IntegralTwoForms.equiv_symbol, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.exteriorSymbol,
    TensorProduct.tmul_smul]
  refine (congrArg (ExteriorPowerCongr.ExteriorBaseChange.powerCongr 2
      (KaehlerDifferential.tensorKaehlerEquiv R S A B))
    (ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerEquiv_tmul_ιMulti A B (KaehlerDifferential R A) 2
      (a • b) (fun i => KaehlerDifferential.D R A (v i)))).trans ?_
  rw [map_smul, ExteriorPowerCongr.ExteriorBaseChange.powerCongr_ιMulti]
  have h : (fun i => KaehlerDifferential.tensorKaehlerEquiv R S A B
      (1 ⊗ₜ[A] KaehlerDifferential.D R A (v i))) =
      fun i => KaehlerDifferential.D S B (algebraMap A B (v i)) := by
    funext i
    exact (KaehlerDifferential.tensorKaehlerEquiv_tmul_D R S A B 1 (v i)).trans (one_smul B _)
  rw [h, Algebra.smul_def, mul_comm]

def scalarEquiv : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 2 ≃ₗ[S] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S B 2 :=
  (Algebra.IsPushout.cancelBaseChange R S A B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 2)).symm.trans
    ((tensorEquiv R S A B).restrictScalars S)

theorem scalarEquiv_symbol (s : S) (a : A) (v : Fin 2 → A) :
    scalarEquiv R S A B (s ⊗ₜ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S B (algebraMap S B s * algebraMap A B a) (fun i => algebraMap A B (v i)) := by
  change tensorEquiv R S A B
    ((Algebra.IsPushout.cancelBaseChange R S A B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 2)).symm
      (s ⊗ₜ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) = _
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul, tensorEquiv_symbol]

theorem scalarEquiv_eq_map :
    (scalarEquiv R S A B).toLinearMap = Forms.ScalarMap.FormsBaseChange.formScalarMap R S A B 2 := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s ω
  obtain ⟨x, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A 2).mkQ_surjective ω
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  | single v a =>
    exact (scalarEquiv_symbol R S A B s a v).trans
      (Forms.ScalarMap.FormsBaseChange.formScalarMap_symbol R S A B s a v).symm

theorem differential_compatibility (x : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 1) :
    scalarEquiv R S A B ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A 1).baseChange S x) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential S B 1 (LowDegreeBaseChange.IntegralLowDegreeBaseChange.oneEquiv R S A B x) := by
  change (scalarEquiv R S A B).toLinearMap ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A 1).baseChange S x) =
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential S B 1 ((LowDegreeBaseChange.IntegralLowDegreeBaseChange.oneEquiv R S A B).toLinearMap x)
  rw [scalarEquiv_eq_map, LowDegreeBaseChange.IntegralLowDegreeBaseChange.one_eq_map]
  exact Forms.ScalarMap.FormsBaseChange.formScalarMap_differential R S A B 1 x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.TwoFormsBaseChange.IntegralTwoFormsBaseChange
