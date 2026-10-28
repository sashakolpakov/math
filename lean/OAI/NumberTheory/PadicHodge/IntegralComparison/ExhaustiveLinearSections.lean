import OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustivePresheafSections
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Pi

/-! # Exhaustive Linear Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustiveLinearSections

noncomputable section

/-!
# IntegralComparison: coefficient-linear reconstruction from all bounded section groups
-/

open _root_.CategoryTheory

open OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustivePresheafSections

universe u v w z t

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
  [Preadditive D] (R : Type t) [CommRing R] [Linear R D]
  (P : ℕ → ObjectProperty C) (hP : Monotone P) (hC : ∀ U, ∃ n, P n U)
  (M : D) (F : Cᵒᵖ ⥤ D)

def compatibleSubmodule : Submodule R (∀ n, ExhaustivePresheafSections.Stage P M F n) where
  carrier := ExhaustivePresheafSections.Compatible P hP M F
  zero_mem' := by
    intro n m hnm
    apply NatTrans.ext
    funext U
    rfl
  add_mem' {a b} ha hb := by
    intro n m hnm
    exact congrArg₂ (· + ·) (ha n m hnm) (hb n m hnm)
  smul_mem' r a ha := by
    intro n m hnm
    exact congrArg (fun t => r • t) (ha n m hnm)

def linearEquiv : ((Functor.const Cᵒᵖ).obj M ⟶ F) ≃ₗ[R] compatibleSubmodule R P hP M F where
  toFun a := ⟨ExhaustivePresheafSections.restrictGlobal P M F a, ExhaustivePresheafSections.restrictGlobal_compatible P hP M F a⟩
  invFun a := ExhaustivePresheafSections.assemble P hP hC M F a.val a.property
  left_inv := ExhaustivePresheafSections.assemble_restrictGlobal P hP hC M F
  right_inv a := Subtype.ext (funext (ExhaustivePresheafSections.restrictGlobal_assemble P hP hC M F a.val a.property))
  map_add' _ _ := Subtype.ext (funext (fun _ => rfl))
  map_smul' _ _ := Subtype.ext (funext (fun _ => rfl))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustiveLinearSections
