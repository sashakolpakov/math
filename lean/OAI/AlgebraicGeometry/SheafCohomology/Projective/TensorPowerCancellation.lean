import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # Tensor Power Cancellation -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorPowerCancellation

noncomputable section

/-! Cancellation of recursively formed tensor powers of inverse objects. -/

open _root_.CategoryTheory MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

def tensorSwapMiddleIso (A B D E : C) :
    (A ⊗ B) ⊗ (D ⊗ E) ≅ (A ⊗ D) ⊗ (B ⊗ E) where
  hom := tensorμ A B D E
  inv := tensorδ A B D E
  hom_inv_id := tensorμ_tensorδ A B D E
  inv_hom_id := tensorδ_tensorμ A B D E

def pairedTensorPowersIso (M N : C) (e : M ⊗ N ≅ 𝟙_ C)
    (P Q : ℕ → C) (p0 : P 0 ≅ 𝟙_ C) (q0 : Q 0 ≅ 𝟙_ C)
    (ps : ∀ n, P (n + 1) ≅ P n ⊗ M)
    (qs : ∀ n, Q (n + 1) ≅ Q n ⊗ N) : ∀ n, P n ⊗ Q n ≅ 𝟙_ C
  | 0 => (p0 ⊗ᵢ q0) ≪≫ λ_ (𝟙_ C)
  | n + 1 => (ps n ⊗ᵢ qs n) ≪≫ tensorSwapMiddleIso (P n) M (Q n) N ≪≫
      (pairedTensorPowersIso M N e P Q p0 q0 ps qs n ⊗ᵢ e) ≪≫ λ_ (𝟙_ C)

theorem pairedTensorPowersIso_succ_hom (M N : C) (e : M ⊗ N ≅ 𝟙_ C)
    (P Q : ℕ → C) (p0 : P 0 ≅ 𝟙_ C) (q0 : Q 0 ≅ 𝟙_ C)
    (ps : ∀ n, P (n + 1) ≅ P n ⊗ M)
    (qs : ∀ n, Q (n + 1) ≅ Q n ⊗ N) (n : ℕ) :
    (TensorPowerCancellation.pairedTensorPowersIso M N e P Q p0 q0 ps qs (n + 1)).hom =
      ((ps n).hom ⊗ₘ (qs n).hom) ≫ tensorμ (P n) M (Q n) N ≫
        ((TensorPowerCancellation.pairedTensorPowersIso M N e P Q p0 q0 ps qs n).hom ⊗ₘ e.hom) ≫
          (λ_ (𝟙_ C)).hom := rfl

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorPowerCancellation
