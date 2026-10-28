import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.KernelQuotient
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Lattices
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Isogeny

/-! # Scaled Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ScaledKernel

noncomputable section

/-! The actual kernel at level q^n is detected by the isogeny preimage
lattice on vectors q^(-n) x. This retains the kernel embedding, beyond
the abstract isomorphism type of the finite quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

universe u

namespace Tate

variable (q : ℕ) [Fact q.Prime] {H : Type u} [AddCommGroup H]

def dividedIntegralVector (n : ℕ) (x : Add.Tate.Module (H := H) q) : Isogeny.Tate.RationalModule q H :=
  ((q : ℚ_[q]) ^ n)⁻¹ • (1 ⊗ₜ[ℤ_[q]] x)

theorem qPower_smul_integral (n : ℕ) (x : Add.Tate.Module (H := H) q) :
    (q : ℚ_[q]) ^ n • ((1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] x) =
      (1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] ((q : ℤ_[q]) ^ n • x) := by
  simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  exact (_root_.map_nsmul (TensorProduct.mk ℤ_[q] ℚ_[q] (Add.Tate.Module (H := H) q) 1) (q ^ n) x).symm

theorem dividedIntegralVector_mem_iff (n : ℕ) (x : Add.Tate.Module (H := H) q) :
    dividedIntegralVector q n x ∈ (TensorProduct.mk ℤ_[q] ℚ_[q] (Add.Tate.Module (H := H) q) 1).range ↔
      Evaluation.Tate.evaluate q n x = 0 := by
  have hn : (q : ℚ_[q]) ^ n ≠ 0 := pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
  rw [Evaluation.Tate.evaluate_eq_zero_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, Isogeny.Tate.integralEmbedding_injective q ?_⟩
    change 1 ⊗ₜ[ℤ_[q]] ((q : ℤ_[q]) ^ n • y) = 1 ⊗ₜ[ℤ_[q]] x
    rw [← qPower_smul_integral]
    change 1 ⊗ₜ[ℤ_[q]] y = ((q : ℚ_[q]) ^ n)⁻¹ • (1 ⊗ₜ[ℤ_[q]] x) at hy
    rw [hy]
    exact smul_inv_smul₀ hn _
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    change 1 ⊗ₜ[ℤ_[q]] y = ((q : ℚ_[q]) ^ n)⁻¹ •
      (1 ⊗ₜ[ℤ_[q]] ((q : ℤ_[q]) ^ n • y))
    rw [← qPower_smul_integral]
    exact (inv_smul_smul₀ hn _).symm

end Tate

variable {S : Scheme.{u}} {A B : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  (T : Over S) (q : ℕ) [Fact q.Prime] (f : A ⟶ B) [IsMonHom f]

theorem dividedIntegralVector_mem_preimage_iff (n : ℕ) (x : Add.schemeTateModule A T q) :
    Tate.dividedIntegralVector q n x ∈ Rational.isogenyTatePreimage (T := T) (q := q) f ↔
      (x.val n).val.toMul ≫ f = 1 := by
  change Rational.rationalTateMap (T := T) (q := q) f
    (((q : ℚ_[q]) ^ n)⁻¹ • (1 ⊗ₜ[ℤ_[q]] x)) ∈ Rational.integralTateImage B T q ↔ _
  rw [LinearMap.map_smul, Lattices.rationalTateMap_integral]
  change Tate.dividedIntegralVector q n (Add.schemeTateMap A T q f x) ∈
    (TensorProduct.mk ℤ_[q] ℚ_[q] (Add.schemeTateModule B T q) 1).range ↔ _
  rw [Tate.dividedIntegralVector_mem_iff]
  constructor
  · intro h
    exact congrArg (fun z : Add.Tate.torsion q (Additive (T ⟶ B)) n => z.val.toMul) h
  · intro h
    apply Subtype.ext
    exact congrArg Additive.ofMul h

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ScaledKernel
