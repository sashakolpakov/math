import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.TensorEquivalence
import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarMap
import Mathlib.RingTheory.Flat.Stability

/-! # Scalar Equivalence -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarEquivalence.FormsBaseChange

noncomputable section

/-! Flat affine scalar extension identifies the actual differential-form complexes, with the canonical symbol formulas in every degree. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation
open scoped TensorProduct

universe u

variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
  [Algebra ℚ A] [Algebra ℚ B] [Module.Flat R S]

local instance coefficientsInvertibleTwo : Invertible (2 : A) := by
  letI : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  exact (Invertible.map (algebraMap ℚ A) (2 : ℚ)).copy 2 (map_ofNat _ _).symm

omit [Algebra ℚ A] [Algebra ℚ B] in
include R S in
theorem affineFlat : Module.Flat A B := by
  let : Algebra.IsPushout R A S B := Algebra.IsPushout.symm inferInstance
  exact Module.Flat.of_linearEquiv (Algebra.IsPushout.equiv R A S B).symm.toLinearEquiv

def formsScalarEquiv (n : ℕ) : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n ≃ₗ[S] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S B n := by
  let : Module.Flat A B := affineFlat R S A B
  exact (Algebra.IsPushout.cancelBaseChange R S A B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n)).symm.trans
    ((TensorEquivalence.FormsBaseChange.formsTensorEquiv R S A B n).restrictScalars S)

theorem formsScalarEquiv_symbol (n : ℕ) (s : S) (a : A) (v : Fin n → A) :
    formsScalarEquiv R S A B n (s ⊗ₜ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S B (algebraMap S B s * algebraMap A B a) (fun i => algebraMap A B (v i)) := by
  let : Module.Flat A B := affineFlat R S A B
  change TensorEquivalence.FormsBaseChange.formsTensorEquiv R S A B n
    ((Algebra.IsPushout.cancelBaseChange R S A B (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n)).symm
      (s ⊗ₜ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) = _
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul, TensorEquivalence.FormsBaseChange.formsTensorEquiv_symbol]

theorem formsScalarEquiv_eq_map (n : ℕ) :
    (formsScalarEquiv R S A B n).toLinearMap = ScalarMap.FormsBaseChange.formScalarMap R S A B n := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s ω
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n) ω
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  | single v a =>
    exact (formsScalarEquiv_symbol R S A B n s a v).trans (ScalarMap.FormsBaseChange.formScalarMap_symbol R S A B s a v).symm

theorem formsScalarEquiv_differential (n : ℕ) (x : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    formsScalarEquiv R S A B (n + 1) ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A n).baseChange S x) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential S B n (formsScalarEquiv R S A B n x) := by
  change (formsScalarEquiv R S A B (n + 1)).toLinearMap
    ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A n).baseChange S x) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential S B n ((formsScalarEquiv R S A B n).toLinearMap x)
  rw [formsScalarEquiv_eq_map, formsScalarEquiv_eq_map]
  exact ScalarMap.FormsBaseChange.formScalarMap_differential R S A B n x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarEquivalence.FormsBaseChange
