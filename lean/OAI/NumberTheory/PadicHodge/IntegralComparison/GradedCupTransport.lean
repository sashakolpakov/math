import Mathlib.LinearAlgebra.BilinearMap

/-! # Graded Cup Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupTransport

noncomputable section

/-! Algebra laws for a graded bilinear cup transported through actual
degreewise linear equivalences. -/

universe u v w

variable (R : Type u) [CommRing R] (H : ℕ → Type v)
  [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]

def degreeCast {m n : ℕ} (h : m = n) : H m ≃ₗ[R] H n := h ▸ LinearEquiv.refl R (H m)

variable (G : ℕ → Type w) [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]

theorem degreeCast_map (f : ∀ i, H i →ₗ[R] G i) {m n : ℕ} (h : m = n) (x : H m) :
    degreeCast R G h (f m x) = f n (degreeCast R H h x) := by
  subst n
  rfl

variable (e : ∀ i, H i ≃ₗ[R] G i)
  (μ : ∀ i j, H i →ₗ[R] H j →ₗ[R] H (i + j))

def cup (i j : ℕ) : G i →ₗ[R] G j →ₗ[R] G (i + j) :=
  (((μ i j).comp (e i).symm.toLinearMap).compl₂ (e j).symm.toLinearMap).compr₂
    (e (i + j)).toLinearMap

theorem cup_apply (i j : ℕ) (x : H i) (y : H j) :
    cup R H G e μ i j (e i x) (e j y) = e (i + j) (μ i j x y) := by
  simp only [cup, LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

theorem assoc (hμ : ∀ i j k (x : H i) (y : H j) (z : H k),
    degreeCast R H (Nat.add_assoc i j k) (μ (i + j) k (μ i j x y) z) = μ i (j + k) x (μ j k y z))
    (i j k : ℕ) (x : G i) (y : G j) (z : G k) :
    degreeCast R G (Nat.add_assoc i j k)
      (cup R H G e μ (i + j) k (cup R H G e μ i j x y) z) =
      cup R H G e μ i (j + k) x (cup R H G e μ j k y z) := by
  obtain ⟨x, rfl⟩ := (e i).surjective x
  obtain ⟨y, rfl⟩ := (e j).surjective y
  obtain ⟨z, rfl⟩ := (e k).surjective z
  rw [cup_apply, cup_apply, cup_apply, cup_apply]
  exact (degreeCast_map R H G (fun n => (e n).toLinearMap) (Nat.add_assoc i j k) _).trans
    (congrArg (e (i + (j + k))) (hμ i j k x y z))

theorem one_add_swap (hμ : ∀ x y : H 1, μ 1 1 x y + μ 1 1 y x = 0)
    (x y : G 1) : cup R H G e μ 1 1 x y + cup R H G e μ 1 1 y x = 0 := by
  obtain ⟨x, rfl⟩ := (e 1).surjective x
  obtain ⟨y, rfl⟩ := (e 1).surjective y
  rw [cup_apply, cup_apply, ← map_add, hμ, map_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupTransport
