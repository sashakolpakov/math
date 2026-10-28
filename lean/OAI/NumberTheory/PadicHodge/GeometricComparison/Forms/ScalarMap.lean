import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.BaseRingMap
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Scalar Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarMap.FormsBaseChange

noncomputable section

/-! The canonical affine scalar-extension map on actual forms in all degrees. -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal
open scoped TensorProduct

universe u

variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B]

def formExtensionMap (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n →ₗ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S B n :=
  ((BaseRingMap.FormsBaseChange.formBaseMap R S B n).restrictScalars R).comp
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (IsScalarTower.toAlgHom R A B)) n)

theorem formExtensionMap_symbol {n : ℕ} (a : A) (v : Fin n → A) :
    formExtensionMap R S A B n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S B (algebraMap A B a) (fun i => algebraMap A B (v i)) := by
  change BaseRingMap.FormsBaseChange.formBaseMap R S B n
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (IsScalarTower.toAlgHom R A B)) n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) = _
  rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol, BaseRingMap.FormsBaseChange.formBaseMap_symbol]
  rfl

theorem formExtensionMap_differential (n : ℕ) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    formExtensionMap R S A B (n + 1) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A n ω) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential S B n (formExtensionMap R S A B n ω) := by
  change BaseRingMap.FormsBaseChange.formBaseMap R S B (n + 1)
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (IsScalarTower.toAlgHom R A B)) (n + 1)
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A n ω)) = _
  rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_differential, BaseRingMap.FormsBaseChange.formBaseMap_differential]
  rfl

def formScalarMap (n : ℕ) : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n →ₗ[S] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S B n :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton S _ (formExtensionMap R S A B n))

theorem formScalarMap_tmul {n : ℕ} (s : S) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    formScalarMap R S A B n (s ⊗ₜ[R] ω) = s • formExtensionMap R S A B n ω := rfl

theorem formScalarMap_symbol {n : ℕ} (s : S) (a : A) (v : Fin n → A) :
    formScalarMap R S A B n (s ⊗ₜ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S B (algebraMap S B s * algebraMap A B a) (fun i => algebraMap A B (v i)) := by
  rw [formScalarMap_tmul, formExtensionMap_symbol,
    ← IsScalarTower.algebraMap_smul B s, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one, smul_smul,
    ← AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one]

theorem formScalarMap_differential (n : ℕ) (x : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    formScalarMap R S A B (n + 1) ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A n).baseChange S x) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential S B n (formScalarMap R S A B n x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s ω =>
    rw [LinearMap.baseChange_tmul, formScalarMap_tmul, formScalarMap_tmul,
      map_smul, formExtensionMap_differential]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarMap.FormsBaseChange
