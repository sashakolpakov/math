import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-! # Supported Cochains -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SupportedCochains.Cech

noncomputable section

/-! Support-restricted Cech cochains with arbitrary additive coefficients. -/

open scoped BigOperators

variable {ι V : Type} [DecidableEq ι] [AddCommGroup V]

def supportCechDelete {q : ℕ} (t : Fin (q + 2) → ι) (k : Fin (q + 2)) : Fin (q + 1) → ι :=
  t ∘ (SimplexCategory.δ k).toOrderHom

theorem supportCechDelete_range_subset {q : ℕ} (t : Fin (q + 2) → ι) (k : Fin (q + 2)) :
    Finset.univ.image (supportCechDelete t k) ⊆ Finset.univ.image t := by
  intro j hj
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hj
  exact Finset.mem_image.mpr ⟨(SimplexCategory.δ k).toOrderHom l, Finset.mem_univ _, rfl⟩

def supportedCechCochains (V : Type) [AddCommGroup V] (N : Finset ι) (q : ℕ) :
    AddSubgroup ((Fin (q + 1) → ι) → V) where
  carrier := {s | ∀ t, ¬N ⊆ Finset.univ.image t → s t = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro s t hs ht a ha
    change s a + t a = 0
    rw [hs a ha, ht a ha, add_zero]
  neg_mem' := by
    intro s hs a ha
    change -s a = 0
    rw [hs a ha, neg_zero]

def supportedCechDifferential (N : Finset ι) (q : ℕ) :
    supportedCechCochains V N q →+ supportedCechCochains V N (q + 1) where
  toFun s := ⟨fun t => ∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val • s.val (supportCechDelete t k), by
    intro t ht
    apply Finset.sum_eq_zero
    intro k _
    rw [s.property _ (fun h => ht (h.trans (supportCechDelete_range_subset t k))), smul_zero]⟩
  map_zero' := by
    apply Subtype.ext
    funext t
    change (∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val • (0 : V)) = 0
    simp only [smul_zero, Finset.sum_const_zero]
  map_add' s t := by
    apply Subtype.ext
    funext a
    change (∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val •
      (s.val (supportCechDelete a k) + t.val (supportCechDelete a k))) =
      (∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val • s.val (supportCechDelete a k)) +
        ∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val • t.val (supportCechDelete a k)
    exact (Finset.sum_congr rfl (fun k _ => smul_add ((-1 : ℤ) ^ k.val)
      (s.val (supportCechDelete a k)) (t.val (supportCechDelete a k)))).trans Finset.sum_add_distrib

theorem supportedCechDifferential_apply (N : Finset ι) (q : ℕ)
    (s : supportedCechCochains V N q) (t : Fin (q + 2) → ι) :
    (supportedCechDifferential N q s).val t =
      ∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val • s.val (supportCechDelete t k) := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.SupportedCochains.Cech
