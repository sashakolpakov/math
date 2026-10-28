import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Ring.Commute

/-! # Signed Five Lemma -/

namespace OAI.AlgebraicTopology.Duality.Poincare.SignedFiveLemma

/-!
# The five lemma with the cap-product connecting sign

Multiplication by a power of minus one is invertible. A diagram whose
connecting square commutes with that sign is therefore changed into a
commutative five-lemma diagram by applying the same sign to the last two
vertical arrows. The middle arrow itself is unchanged.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A power of the integer sign preserves invertibility of a module morphism. -/
theorem isIso_negOnePow_smul {A B : ModuleCat.{0} ℚ} (f : A ⟶ B) [IsIso f] (k : ℕ) :
    IsIso (((-1 : ℤ) ^ k) • f) := by
  rcases neg_one_pow_eq_or ℤ k with h | h
  · simpa only [h, one_smul] using (inferInstance : IsIso f)
  · have hn : IsIso (-f) := (-asIso f).isIso_hom
    simpa only [h, neg_one_smul] using hn

/-- The module five lemma with exactly one signed connecting square. -/
theorem isIso_of_signed_five_lemma
    {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ : ModuleCat.{0} ℚ}
    (f₀ : A₀ ⟶ A₁) (f₁ : A₁ ⟶ A₂) (f₂ : A₂ ⟶ A₃) (f₃ : A₃ ⟶ A₄)
    (g₀ : B₀ ⟶ B₁) (g₁ : B₁ ⟶ B₂) (g₂ : B₂ ⟶ B₃) (g₃ : B₃ ⟶ B₄)
    (a₀ : A₀ ⟶ B₀) (a₁ : A₁ ⟶ B₁) (a₂ : A₂ ⟶ B₂)
    (a₃ : A₃ ⟶ B₃) (a₄ : A₄ ⟶ B₄) (k : ℕ)
    (hA : (ComposableArrows.mk₄ f₀ f₁ f₂ f₃).Exact)
    (hB : (ComposableArrows.mk₄ g₀ g₁ g₂ g₃).Exact)
    (h₀ : f₀ ≫ a₁ = a₀ ≫ g₀) (h₁ : f₁ ≫ a₂ = a₁ ≫ g₁)
    (h₂ : a₂ ≫ g₂ = ((-1 : ℤ) ^ k) • (f₂ ≫ a₃))
    (h₃ : f₃ ≫ a₄ = a₃ ≫ g₃)
    [IsIso a₀] [IsIso a₁] [IsIso a₃] [IsIso a₄] : IsIso a₂ := by
  let : IsIso (((-1 : ℤ) ^ k) • a₃) := isIso_negOnePow_smul a₃ k
  let : IsIso (((-1 : ℤ) ^ k) • a₄) := isIso_negOnePow_smul a₄ k
  let φ : ComposableArrows.mk₄ f₀ f₁ f₂ f₃ ⟶ ComposableArrows.mk₄ g₀ g₁ g₂ g₃ :=
    ComposableArrows.homMk₄ a₀ a₁ a₂ (((-1 : ℤ) ^ k) • a₃) (((-1 : ℤ) ^ k) • a₄)
      h₀ h₁ (by
        change f₂ ≫ (((-1 : ℤ) ^ k) • a₃) = a₂ ≫ g₂
        rw [Preadditive.comp_zsmul]
        exact h₂.symm) (by
        change f₃ ≫ (((-1 : ℤ) ^ k) • a₄) = (((-1 : ℤ) ^ k) • a₃) ≫ g₃
        rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, h₃])
  have h : IsIso (ComposableArrows.app' φ 2) :=
    CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hA hB φ
      (by change Epi a₀; infer_instance)
      (by change IsIso a₁; infer_instance)
      (by change IsIso (((-1 : ℤ) ^ k) • a₃); infer_instance)
      (by change Mono (((-1 : ℤ) ^ k) • a₄); infer_instance)
  exact h

end OAI.AlgebraicTopology.Duality.Poincare.SignedFiveLemma
