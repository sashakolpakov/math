import OAI.AlgebraicGeometry.Comparison.Betti.SupportedCochains
import Mathlib.Tactic.Abel

/-! # Supported Cochain Contraction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SupportedCochainContraction.Cech

noncomputable section

/-! Prepending an index outside the required support contracts positive-degree cycles. -/

open scoped BigOperators

variable {ι V : Type} [DecidableEq ι] [AddCommGroup V]

def supportCechPrepend {q : ℕ} (i : ι) (t : Fin (q + 1) → ι) : Fin (q + 2) → ι := Fin.cases i t

omit [DecidableEq ι] in
theorem supportCechDelete_prepend_zero {q : ℕ} (i : ι) (t : Fin (q + 1) → ι) :
    SupportedCochains.Cech.supportCechDelete (supportCechPrepend i t) 0 = t := by
  funext k
  rfl

omit [DecidableEq ι] in
theorem supportCechDelete_prepend_succ {q : ℕ} (i : ι) (t : Fin (q + 2) → ι) (k : Fin (q + 2)) :
    SupportedCochains.Cech.supportCechDelete (supportCechPrepend i t) k.succ = supportCechPrepend i (SupportedCochains.Cech.supportCechDelete t k) := by
  funext l
  refine Fin.cases ?_ (fun m => ?_) l
  · rfl
  · simp [SupportedCochains.Cech.supportCechDelete, supportCechPrepend, SimplexCategory.δ, Function.comp_apply]

theorem supportCechPrepend_not_subset {N : Finset ι} {i : ι} (hi : i ∉ N)
    {q : ℕ} (t : Fin (q + 1) → ι) (ht : ¬N ⊆ Finset.univ.image t) :
    ¬N ⊆ Finset.univ.image (supportCechPrepend i t) := by
  intro h
  apply ht
  intro j hj
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (h hj)
  induction k using Fin.cases with
  | zero =>
    have hij : i = j := hk
    exact False.elim (hi (hij.symm ▸ hj))
  | succ k =>
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩

def supportedCechContraction (N : Finset ι) (i : ι) (hi : i ∉ N) (q : ℕ) :
    SupportedCochains.Cech.supportedCechCochains V N (q + 1) →+ SupportedCochains.Cech.supportedCechCochains V N q where
  toFun s := ⟨fun t => s.val (supportCechPrepend i t),
    fun t ht => s.property _ (supportCechPrepend_not_subset hi t ht)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem supportedCechContraction_homotopy (N : Finset ι) (i : ι) (hi : i ∉ N) (q : ℕ)
    (s : SupportedCochains.Cech.supportedCechCochains V N (q + 1)) :
    SupportedCochains.Cech.supportedCechDifferential N q (supportedCechContraction N i hi q s) +
      supportedCechContraction N i hi (q + 1) (SupportedCochains.Cech.supportedCechDifferential N (q + 1) s) = s := by
  apply Subtype.ext
  funext t
  change (∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val •
      s.val (supportCechPrepend i (SupportedCochains.Cech.supportCechDelete t k))) +
    ∑ k : Fin (q + 3), (-1 : ℤ) ^ k.val •
      s.val (SupportedCochains.Cech.supportCechDelete (supportCechPrepend i t) k) = s.val t
  conv_lhs =>
    rhs
    rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ,
    mul_neg, mul_one, neg_smul, supportCechDelete_prepend_zero, supportCechDelete_prepend_succ]
  rw [Finset.sum_neg_distrib]
  abel

theorem supportedCechContraction_cycle (N : Finset ι) (i : ι) (hi : i ∉ N) (q : ℕ)
    (s : SupportedCochains.Cech.supportedCechCochains V N (q + 1)) (hs : SupportedCochains.Cech.supportedCechDifferential N (q + 1) s = 0) :
    SupportedCochains.Cech.supportedCechDifferential N q (supportedCechContraction N i hi q s) = s := by
  have h := supportedCechContraction_homotopy N i hi q s
  rw [hs, map_zero, add_zero] at h
  exact h

theorem supportedCechCycle_has_primitive (N : Finset ι) (i : ι) (hi : i ∉ N) (q : ℕ)
    (s : SupportedCochains.Cech.supportedCechCochains V N (q + 1)) (hs : SupportedCochains.Cech.supportedCechDifferential N (q + 1) s = 0) :
    ∃ t : SupportedCochains.Cech.supportedCechCochains V N q, SupportedCochains.Cech.supportedCechDifferential N q t = s := by
  exact ⟨supportedCechContraction N i hi q s, supportedCechContraction_cycle N i hi q s hs⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.SupportedCochainContraction.Cech
