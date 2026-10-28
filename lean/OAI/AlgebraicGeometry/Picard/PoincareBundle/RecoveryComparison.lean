import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Recovery Comparison -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.RecoveryComparison

noncomputable section

/-!
# Two uniquely recovering objects have isomorphic pullback comparisons
-/

open _root_.CategoryTheory

variable {C D : Type*} [Category C] [Category D]

/-- Maps between two recovery objects are inverse when their pullback factorizations are unique. -/
def recoveryIso (L : C ⥤ D) {N I : C} {M : D} (e : L.obj N ≅ M) (c : L.obj I ⟶ M)
    (k : N ⟶ I) (d : I ⟶ N) (hk : L.map k ≫ c = e.hom) (hd : L.map d ≫ e.hom = c)
    (hN : ∀ a : N ⟶ N, L.map a ≫ e.hom = e.hom → a = 𝟙 N)
    (hI : ∀ a : I ⟶ I, L.map a ≫ c = c → a = 𝟙 I) : N ≅ I where
  hom := k
  inv := d
  hom_inv_id := hN (k ≫ d) (by rw [L.map_comp, Category.assoc, hd, hk])
  inv_hom_id := hI (d ≫ k) (by rw [L.map_comp, Category.assoc, hk, hd])

/-- The canonical comparison is an isomorphism once both recovery properties are established. -/
theorem comparison_isIso (L : C ⥤ D) {N I : C} {M : D} (e : L.obj N ≅ M) (c : L.obj I ⟶ M)
    (k : N ⟶ I) (d : I ⟶ N) (hk : L.map k ≫ c = e.hom) (hd : L.map d ≫ e.hom = c)
    (hN : ∀ a : N ⟶ N, L.map a ≫ e.hom = e.hom → a = 𝟙 N)
    (hI : ∀ a : I ⟶ I, L.map a ≫ c = c → a = 𝟙 I) : IsIso c := by
  let v := recoveryIso L e c k d hk hd hN hI
  have : IsIso d := show IsIso v.inv from inferInstance
  have hc : IsIso (L.map d ≫ e.hom) := inferInstance
  exact hd ▸ hc

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.RecoveryComparison
