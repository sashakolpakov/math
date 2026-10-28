import OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.TateNaturality
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TateAction
import OAI.NumberTheory.PadicHodge.GeometricComparison.TateEndomorphismTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.DeterminantPolynomialResultant
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Algebraic Tate Polynomial Action -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraicTatePolynomialAction

noncomputable section

/-! The genuine algebraic endomorphism ring acts on the actual Tate module.
Polynomial evaluation and scalar extension preserve this action, so its
determinants are resultants of its original characteristic polynomial. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TateAction

universe u
variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
  (T : Over S) (ℓ : ℕ) [Fact ℓ.Prime]

def endHom : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A →+* Module.End ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.schemeTateModule A T ℓ) :=
  (AlgebraicGeometry.AbelianScheme.TateComparison.TateAction.tateEndMap A T ℓ).comp (GeometricComparison.TateEndomorphismTransport.Comparison.integralEndEquiv A).symm.toRingHom

theorem schemeTateMap_eq_of_eq (f g : A ⟶ A) [IsMonHom f] [IsMonHom g] (h : f = g) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Add.schemeTateMap A T ℓ f = AlgebraicGeometry.AbelianScheme.TateComparison.Add.schemeTateMap A T ℓ g := by
  subst g
  rfl

theorem endHom_apply (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    endHom A T ℓ F = AlgebraicGeometry.AbelianScheme.TateComparison.Add.schemeTateMap A T ℓ F.toMul.hom.hom := by
  change AlgebraicGeometry.AbelianScheme.TateComparison.TateAction.tateEndMap A T ℓ ((GeometricComparison.TateEndomorphismTransport.Comparison.integralEndEquiv A).symm F) = _
  rw [AlgebraicGeometry.AbelianScheme.TateComparison.TateAction.tateEndMap_eq_schemeTateMap]
  apply schemeTateMap_eq_of_eq
  have h := GeometricComparison.TateEndomorphismTransport.Comparison.integralEndEquiv_schemeMap A
    ((GeometricComparison.TateEndomorphismTransport.Comparison.integralEndEquiv A).symm F)
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

theorem endHom_eval₂_nat (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (P : Polynomial ℕ) :
    endHom A T ℓ (P.eval₂ (Nat.castRingHom _) F) =
      Polynomial.aeval (endHom A T ℓ F) (P.map (Nat.castRingHom ℤ_[ℓ])) := by
  rw [Polynomial.hom_eval₂, Polynomial.aeval_def, Polynomial.eval₂_map]
  congr 1
  exact Subsingleton.elim _ _

abbrev rationalModule := ℚ_[ℓ] ⊗[ℤ_[ℓ]] AlgebraicGeometry.AbelianScheme.TateComparison.Add.schemeTateModule A T ℓ

def rationalEndHom : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A →+* Module.End ℚ_[ℓ] (rationalModule A T ℓ) where
  toFun F := (endHom A T ℓ F).baseChange ℚ_[ℓ]
  map_zero' := by rw [map_zero, LinearMap.baseChange_zero]
  map_one' := by rw [map_one, LinearMap.baseChange_one]
  map_add' F G := by rw [map_add, LinearMap.baseChange_add]
  map_mul' F G := by rw [map_mul, LinearMap.baseChange_mul]

theorem rationalEndHom_apply (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    rationalEndHom A T ℓ F = (AlgebraicGeometry.AbelianScheme.TateComparison.Add.schemeTateMap A T ℓ F.toMul.hom.hom).baseChange ℚ_[ℓ] := by
  change (endHom A T ℓ F).baseChange ℚ_[ℓ] = _
  apply congrArg
  exact endHom_apply A T ℓ F

theorem rationalEndHom_eval₂_nat (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (P : Polynomial ℕ) :
    rationalEndHom A T ℓ (P.eval₂ (Nat.castRingHom _) F) =
      Polynomial.aeval (rationalEndHom A T ℓ F) (P.map (Nat.castRingHom ℚ_[ℓ])) := by
  rw [Polynomial.hom_eval₂, Polynomial.aeval_def, Polynomial.eval₂_map]
  congr 1
  exact Subsingleton.elim _ _

theorem determinant_eval₂_nat [Module.Finite ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.schemeTateModule A T ℓ)]
    (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (P : Polynomial ℕ) :
    (rationalEndHom A T ℓ (P.eval₂ (Nat.castRingHom _) F)).det =
      (rationalEndHom A T ℓ F).charpoly.resultant (P.map (Nat.castRingHom ℚ_[ℓ])) := by
  rw [rationalEndHom_eval₂_nat]
  exact DeterminantPolynomialResultant.det_aeval _ _

variable {k : Type u} [Field k] [IsAlgClosed k]
  (B : Over (Spec (.of k))) [GrpObj B] [IsCommMonObj B]
  [Smooth B.hom] [IsProper B.hom] [GeometricallyIntegral B.hom]

omit [IsAlgClosed k] [Smooth B.hom] [IsProper B.hom] [GeometricallyIntegral B.hom] in
theorem endHom_eq_tateAction (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd B) :
    endHom B (𝟙_ (Over (Spec (.of k)))) ℓ F =
      Integral.TateNaturality.tateAction ℓ B F :=
  endHom_apply B _ ℓ F

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraicTatePolynomialAction
