import OAI.AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction
import OAI.AlgebraicGeometry.FormalGeometry.Completion.RationalPointLift
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiniteGeneration
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Functor
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Tate Module -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.TateModule

noncomputable section

/-! Finite free Tate modules of actual geometric points in arbitrary
characteristic, at primes invertible in the ground field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Functor

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]

abbrev Points := Additive (𝟙_ (Over (Spec (.of k))) ⟶ A)

theorem divisible (n : ℕ) (hn : (n : k) ≠ 0) (x : Points A) :
    ∃ y : Points A, n • y = x := by
  let m := ((𝟙 A : A ⟶ A) ^ n)
  let : IsFinite m.left := AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.multiplication_isFinite A n hn
  let : Surjective m.left := AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.multiplication_surjective A n hn
  obtain ⟨y, hy⟩ := AlgebraicGeometry.FormalGeometry.Completion.RationalPointLift.Construction.exists_rationalPoint_lift m.left x.toMul.left
  have yw : y ≫ A.hom = 𝟙 _ := by
    rw [← m.w, ← Category.assoc, hy]
    exact x.toMul.w
  let y' : 𝟙_ (Over (Spec (.of k))) ⟶ A := Over.homMk y yw
  have hy' : y' ≫ m = x.toMul := by
    apply Over.OverMorphism.ext
    exact hy
  refine ⟨Additive.ofMul y', ?_⟩
  apply Additive.toMul.injective
  rw [toMul_nsmul]
  change y' ^ n = x.toMul
  simpa only [m, MonObj.comp_pow, Category.comp_id] using hy'

variable (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)

include hℓ

omit [GeometricallyIntegral A.hom] [Fact (Nat.Prime ℓ)] in
theorem torsion_finite (n : ℕ) : Finite (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion ℓ (Points A) n) := by
  let : Finite (AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A (ℓ ^ n)) :=
    AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints_finite A (ℓ ^ n) (by
      rw [Nat.cast_pow]
      exact pow_ne_zero n hℓ)
  let f : AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion ℓ (Points A) n → AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction.Construction.geometricTorsionPoints A (ℓ ^ n) :=
    fun x => ⟨x.val.toMul, congrArg Additive.toMul x.property⟩
  apply Finite.of_injective f
  intro x y h
  apply Subtype.ext
  apply Additive.toMul.injective
  exact congrArg Subtype.val h

theorem finite : Module.Finite ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Points A) ℓ) := by
  let : Finite (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion ℓ (Points A) 1) := torsion_finite A ℓ hℓ 1
  exact AlgebraicGeometry.AbelianScheme.TateComparison.FiniteGeneration.Tate.finite_of_finite_torsion ℓ (divisible A ℓ hℓ)

theorem free : Module.Free ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Points A) ℓ) := by
  let : Module.Finite ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Points A) ℓ) := finite A ℓ hℓ
  infer_instance

theorem evaluate_surjective (n : ℕ) :
    Function.Surjective (AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation.Tate.evaluate (H := Points A) ℓ n) :=
  AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation.Tate.evaluate_surjective ℓ (divisible A ℓ hℓ) n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.TateModule
