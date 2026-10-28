import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ZeroForms
import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarMap
import Mathlib.RingTheory.Kaehler.TensorProduct

/-! # Low Degree Base Change -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.LowDegreeBaseChange.IntegralLowDegreeBaseChange

noncomputable section

/-! Actual degree-zero and degree-one forms commute with arbitrary affine coefficient base change, including reduction modulo the prime. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation
open scoped TensorProduct

universe u

variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]

def zeroEquiv : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 0 ≃ₗ[S] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S B 0 :=
  (((ZeroForms.IntegralZeroForms.equiv R A).restrictScalars R).baseChange R S _ _).trans
    ((Algebra.IsPushout.equiv R S A B).toLinearEquiv.trans
      ((ZeroForms.IntegralZeroForms.equiv S B).restrictScalars S).symm)

def oneEquiv : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 1 ≃ₗ[S] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S B 1 :=
  (((OneForms.IntegralOneForms.equiv R A).restrictScalars R).baseChange R S _ _).trans
    ((KaehlerDifferential.tensorKaehlerEquivBase R S A B).trans
      ((OneForms.IntegralOneForms.equiv S B).restrictScalars S).symm)

theorem zero_symbol (s : S) (a : A) (v : Fin 0 → A) :
    zeroEquiv R S A B (s ⊗ₜ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S B (algebraMap S B s * algebraMap A B a) (fun i => algebraMap A B (v i)) := by
  apply (ZeroForms.IntegralZeroForms.equiv S B).injective
  change ZeroForms.IntegralZeroForms.equiv S B ((ZeroForms.IntegralZeroForms.equiv S B).symm
    (Algebra.IsPushout.equiv R S A B
      (((ZeroForms.IntegralZeroForms.equiv R A).restrictScalars R).baseChange R S _ _
        (s ⊗ₜ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)))) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.baseChange_tmul]
  change Algebra.IsPushout.equiv R S A B (s ⊗ₜ[R] ZeroForms.IntegralZeroForms.toZero R A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) = _
  rw [ZeroForms.IntegralZeroForms.toZero_symbol, Algebra.IsPushout.equiv_tmul]
  exact (ZeroForms.IntegralZeroForms.toZero_symbol S B _ _).symm

theorem one_symbol (s : S) (a : A) (v : Fin 1 → A) :
    oneEquiv R S A B (s ⊗ₜ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S B (algebraMap S B s * algebraMap A B a) (fun i => algebraMap A B (v i)) := by
  apply (OneForms.IntegralOneForms.equiv S B).injective
  change OneForms.IntegralOneForms.equiv S B ((OneForms.IntegralOneForms.equiv S B).symm
    (KaehlerDifferential.tensorKaehlerEquivBase R S A B
      (((OneForms.IntegralOneForms.equiv R A).restrictScalars R).baseChange R S _ _
        (s ⊗ₜ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)))) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.baseChange_tmul]
  change KaehlerDifferential.tensorKaehlerEquivBase R S A B
    (s ⊗ₜ[R] OneForms.IntegralOneForms.toOne R A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) =
      OneForms.IntegralOneForms.toOne S B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S B _ _)
  rw [OneForms.IntegralOneForms.toOne_symbol, KaehlerDifferential.tensorKaehlerEquivBase_tmul,
    map_smul, KaehlerDifferential.map_D, OneForms.IntegralOneForms.toOne_symbol]
  rw [← IsScalarTower.algebraMap_smul B a (KaehlerDifferential.D S B (algebraMap A B (v 0))),
    ← IsScalarTower.algebraMap_smul B s
      (algebraMap A B a • KaehlerDifferential.D S B (algebraMap A B (v 0))), smul_smul]

theorem zero_eq_map : (zeroEquiv R S A B).toLinearMap = Forms.ScalarMap.FormsBaseChange.formScalarMap R S A B 0 := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s ω
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A 0) ω
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  | single v a => exact (zero_symbol R S A B s a v).trans (Forms.ScalarMap.FormsBaseChange.formScalarMap_symbol R S A B s a v).symm

theorem one_eq_map : (oneEquiv R S A B).toLinearMap = Forms.ScalarMap.FormsBaseChange.formScalarMap R S A B 1 := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s ω
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A 1) ω
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  | single v a => exact (one_symbol R S A B s a v).trans (Forms.ScalarMap.FormsBaseChange.formScalarMap_symbol R S A B s a v).symm

theorem differential_compatibility (x : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 0) :
    oneEquiv R S A B ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A 0).baseChange S x) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential S B 0 (zeroEquiv R S A B x) := by
  change (oneEquiv R S A B).toLinearMap ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A 0).baseChange S x) =
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential S B 0 ((zeroEquiv R S A B).toLinearMap x)
  rw [zero_eq_map, one_eq_map]
  exact Forms.ScalarMap.FormsBaseChange.formScalarMap_differential R S A B 0 x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.LowDegreeBaseChange.IntegralLowDegreeBaseChange
