import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.CoordinateLinearity
import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.EtaleEquivalence

/-! # Localization -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.Localization.FormsBaseChange

noncomputable section

/-! Localization of the coordinate algebra localizes the actual differential-form module in every degree. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation
open scoped TensorProduct

universe u

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Algebra ℚ A] [Algebra ℚ B] (T : Submonoid A) [IsLocalization T B]

local instance localizationInvertibleTwo : Invertible (2 : A) := by
  letI : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  exact (Invertible.map (algebraMap ℚ A) (2 : ℚ)).copy 2 (map_ofNat _ _).symm

def localizationFormsEquiv (n : ℕ) : B ⊗[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n ≃ₗ[B] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n := by
  let : Module.Flat A B := IsLocalization.flat B T
  let : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization T
  exact EtaleEquivalence.FormsBaseChange.formsEtaleEquiv R A B n

theorem localizationFormsEquiv_symbol (n : ℕ) (b : B) (a : A) (v : Fin n → A) :
    localizationFormsEquiv R A B T n (b ⊗ₜ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B (b * algebraMap A B a) (fun i => algebraMap A B (v i)) := by
  let : Module.Flat A B := IsLocalization.flat B T
  let : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization T
  exact EtaleEquivalence.FormsBaseChange.formsEtaleEquiv_symbol R A B n b a v

theorem localizationFormsEquiv_one_tmul (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    localizationFormsEquiv R A B T n (1 ⊗ₜ[A] ω) = CoordinateLinearity.FormsBaseChange.coordinateFormMap R A B n ω := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n) ω
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  | single v a =>
    change localizationFormsEquiv R A B T n (1 ⊗ₜ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      CoordinateLinearity.FormsBaseChange.coordinateFormMap R A B n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)
    rw [localizationFormsEquiv_symbol, one_mul, CoordinateLinearity.FormsBaseChange.coordinateFormMap_symbol]

include T in
theorem coordinateFormMap_isBaseChange (n : ℕ) : IsBaseChange B (CoordinateLinearity.FormsBaseChange.coordinateFormMap R A B n) := by
  have h := (TensorProduct.isBaseChange A (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) B).comp
    (IsBaseChange.ofEquiv (localizationFormsEquiv R A B T n))
  have he : ((localizationFormsEquiv R A B T n).toLinearMap.restrictScalars A).comp
      (TensorProduct.mk A B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) 1) = CoordinateLinearity.FormsBaseChange.coordinateFormMap R A B n :=
    LinearMap.ext (localizationFormsEquiv_one_tmul R A B T n)
  exact he ▸ h

theorem coordinateFormMap_isLocalized (n : ℕ) : IsLocalizedModule T (CoordinateLinearity.FormsBaseChange.coordinateFormMap R A B n) :=
  (isLocalizedModule_iff_isBaseChange T B _).mpr (coordinateFormMap_isBaseChange R A B T n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.Localization.FormsBaseChange
