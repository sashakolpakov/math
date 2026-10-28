import OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorInjectivityExtensions
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Tensor Nilpotent Devissage -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorNilpotentDevissage

noncomputable section

/-! Injectivity after tensoring with a residue field implies injectivity
after tensoring with any module killed by a power of its maximal ideal. -/

open TensorProduct

universe u v w z
variable {B : Type u} [CommRing B]
variable {K : Type v} [AddCommGroup K] [Module B K]
variable {F : Type w} [AddCommGroup F] [Module B F]

theorem lTensor_injective_of_maximalIdeal_power (f : K →ₗ[B] F) [Module.Flat B F]
    (m : Ideal B) [m.IsMaximal] (hm : Function.Injective (f.lTensor (B ⧸ m)))
    (n : ℕ) : ∀ (N : Type z) [AddCommGroup N] [Module B N],
      m ^ n • (⊤ : Submodule B N) = ⊥ → Function.Injective (f.lTensor N) := by
  let : Field (B ⧸ m) := Ideal.Quotient.field m
  induction n with
  | zero =>
    intro N _ _ hn
    have htop : (⊤ : Submodule B N) = ⊥ := by simpa using hn
    have hz (x : N) : x = 0 := (Submodule.mem_bot B).mp (htop ▸ Submodule.mem_top)
    let : Subsingleton N := ⟨fun x y => (hz x).trans (hz y).symm⟩
    exact fun _ _ _ => Subsingleton.elim _ _
  | succ n ih =>
    intro N _ _ hn
    let P : Submodule B N := m • ⊤
    have hP : m ^ n • (⊤ : Submodule B P) = ⊥ := by
      apply bot_unique
      intro x hx
      apply (Submodule.mem_bot B).mpr
      apply Subtype.ext
      have hv := (Submodule.mem_smul_top_iff (m ^ n) P x).mp hx
      have he : m ^ n • P = ⊥ := by
        dsimp [P]
        rw [← Submodule.mul_smul, ← pow_succ]
        exact hn
      rw [he] at hv
      exact (Submodule.mem_bot B).mp hv
    have hQ : Function.Injective (f.lTensor (N ⧸ P)) := by
      exact TensorInjectivityExtensions.lTensor_injective_of_flat_scalar_module (B ⧸ m) (N ⧸ P) f hm
    exact TensorInjectivityExtensions.lTensor_injective_of_shortExact f P.subtype P.mkQ P.subtype_injective
      (LinearMap.exact_subtype_mkQ P) P.mkQ_surjective (ih P hP) hQ

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorNilpotentDevissage
