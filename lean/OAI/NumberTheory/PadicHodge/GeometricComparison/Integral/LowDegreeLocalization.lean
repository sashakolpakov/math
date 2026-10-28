import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ZeroForms
import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.CoordinateLinearity
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Localization.BaseChange

/-! # Low Degree Localization -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.LowDegreeLocalization.IntegralLowDegreeLocalization

noncomputable section

/-! Localization of the actual first two form modules over arbitrary base rings. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation
open scoped TensorProduct

universe u

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

def zeroEquiv : B ⊗[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 0 ≃ₗ[B] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B 0 :=
  ((ZeroForms.IntegralZeroForms.equiv R A).baseChange A B _ _).trans
    ((TensorProduct.AlgebraTensorModule.rid A B B).trans (ZeroForms.IntegralZeroForms.equiv R B).symm)

omit [IsScalarTower R A B] in
theorem zero_symbol (b : B) (a : A) (v : Fin 0 → A) :
    zeroEquiv R A B (b ⊗ₜ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B (b * algebraMap A B a) (fun i => algebraMap A B (v i)) := by
  apply (ZeroForms.IntegralZeroForms.equiv R B).injective
  simp only [zeroEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.baseChange_tmul]
  change TensorProduct.AlgebraTensorModule.rid A B B
    (b ⊗ₜ[A] ZeroForms.IntegralZeroForms.toZero R A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) = _
  rw [ZeroForms.IntegralZeroForms.toZero_symbol, TensorProduct.AlgebraTensorModule.rid_tmul]
  change a • b = ZeroForms.IntegralZeroForms.toZero R B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B _ _)
  rw [ZeroForms.IntegralZeroForms.toZero_symbol, Algebra.smul_def, mul_comm]

variable [Algebra.FormallyEtale A B]

def oneEquiv : B ⊗[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A 1 ≃ₗ[B] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B 1 :=
  ((OneForms.IntegralOneForms.equiv R A).baseChange A B _ _).trans
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B).trans
      (OneForms.IntegralOneForms.equiv R B).symm)

theorem one_symbol (b : B) (a : A) (v : Fin 1 → A) :
    oneEquiv R A B (b ⊗ₜ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B (b * algebraMap A B a) (fun i => algebraMap A B (v i)) := by
  apply (OneForms.IntegralOneForms.equiv R B).injective
  simp only [oneEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.baseChange_tmul]
  change KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B
    (b ⊗ₜ[A] OneForms.IntegralOneForms.toOne R A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) =
      OneForms.IntegralOneForms.toOne R B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B _ _)
  rw [OneForms.IntegralOneForms.toOne_symbol,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, OneForms.IntegralOneForms.toOne_symbol,
    map_smul, KaehlerDifferential.map_D]
  rw [← IsScalarTower.algebraMap_smul B a, smul_smul]

def equiv (n : ℕ) (hn : n ≤ 1) : B ⊗[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n ≃ₗ[B] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n := by
  cases n with
  | zero => exact zeroEquiv R A B
  | succ n =>
    have h : n = 0 := by omega
    subst n
    exact oneEquiv R A B

theorem equiv_symbol (n : ℕ) (hn : n ≤ 1) (b : B) (a : A) (v : Fin n → A) :
    equiv R A B n hn (b ⊗ₜ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B (b * algebraMap A B a) (fun i => algebraMap A B (v i)) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
  · exact zero_symbol R A B b a v
  · exact one_symbol R A B b a v

theorem equiv_one_tmul (n : ℕ) (hn : n ≤ 1) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    equiv R A B n hn (1 ⊗ₜ[A] ω) = Forms.CoordinateLinearity.FormsBaseChange.coordinateFormMap R A B n ω := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n) ω
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  | single v a =>
    change equiv R A B n hn (1 ⊗ₜ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      Forms.CoordinateLinearity.FormsBaseChange.coordinateFormMap R A B n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)
    rw [equiv_symbol, one_mul, Forms.CoordinateLinearity.FormsBaseChange.coordinateFormMap_symbol]

theorem isBaseChange (n : ℕ) (hn : n ≤ 1) :
    IsBaseChange B (Forms.CoordinateLinearity.FormsBaseChange.coordinateFormMap R A B n) := by
  have h := (TensorProduct.isBaseChange A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) B).comp
    (IsBaseChange.ofEquiv (equiv R A B n hn))
  have he : ((equiv R A B n hn).toLinearMap.restrictScalars A).comp
      (TensorProduct.mk A B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) 1) = Forms.CoordinateLinearity.FormsBaseChange.coordinateFormMap R A B n :=
    LinearMap.ext (equiv_one_tmul R A B n hn)
  exact he ▸ h

omit [Algebra.FormallyEtale A B] in
theorem isLocalized (T : Submonoid A) [IsLocalization T B] (n : ℕ) (hn : n ≤ 1) :
    IsLocalizedModule T (Forms.CoordinateLinearity.FormsBaseChange.coordinateFormMap R A B n) := by
  let : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization T
  exact (isLocalizedModule_iff_isBaseChange T B _).mpr (IntegralLowDegreeLocalization.isBaseChange R A B n hn)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.LowDegreeLocalization.IntegralLowDegreeLocalization
