import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.FieldTheory.Separable
import Mathlib.Data.Set.Card

/-! # Monic Roots -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.MonicRoots.Constructions.RootPolynomials

noncomputable section

/-!
# Monic polynomials determined and bounded by their roots

For a monic separable complex polynomial, the set of roots determines the
polynomial. A uniform root bound also bounds every coefficient.
-/

open Set _root_.Polynomial

theorem eq_of_same_roots {P Q : ℂ[X]} (hP : P.Monic) (hQ : Q.Monic)
    (hPs : P.Separable) (hQs : Q.Separable)
    (hroots : ∀ z : ℂ, P.eval z = 0 ↔ Q.eval z = 0) : P = Q := by
  have hr : P.roots = Q.roots := (Multiset.Nodup.ext (nodup_roots hPs) (nodup_roots hQs)).mpr
    (fun z => by simpa only [mem_roots hP.ne_zero, mem_roots hQ.ne_zero, IsRoot] using hroots z)
  rw [(IsAlgClosed.splits P).eq_prod_roots_of_monic hP,
    (IsAlgClosed.splits Q).eq_prod_roots_of_monic hQ, hr]

theorem ncard_zero_set {P : ℂ[X]} (hP : P ≠ 0) (hPs : P.Separable) :
    {z : ℂ | P.eval z = 0}.ncard = P.natDegree := by
  classical
  have hset : {z : ℂ | P.eval z = 0} = (P.roots.toFinset : Set ℂ) := by
    ext z
    simp only [mem_ofPred_eq, Finset.mem_coe, Multiset.mem_toFinset, mem_roots hP, IsRoot]
  rw [hset, Set.ncard_coe_finset, Multiset.toFinset_card_of_nodup (nodup_roots hPs),
    ← (IsAlgClosed.splits P).natDegree_eq_card_roots]

theorem norm_coeff_le_of_roots_bounded {P : ℂ[X]} (hP : P.Monic) {M : ℝ}
    (hroots : ∀ z : ℂ, P.eval z = 0 → ‖z‖ ≤ M) (j : ℕ) :
    ‖P.coeff j‖ ≤ (P.natDegree.choose j : ℝ) * (max 1 M) ^ P.natDegree := by
  apply (P.norm_coeff_le_choose_mul_mahlerMeasure j).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, hP.leadingCoeff, norm_one, one_mul,
    (IsAlgClosed.splits P).natDegree_eq_card_roots]
  calc
    _ ≤ (P.roots.map (fun _ : ℂ => max (1 : ℝ) M)).prod :=
      Multiset.prod_map_le_prod_map₀ _ _
        (fun _ _ => zero_le_one.trans (le_max_left _ _))
        (fun z hz => max_le_max le_rfl (hroots z ((mem_roots hP.ne_zero).mp hz)))
    _ = _ := by
      change (P.roots.map (Function.const ℂ (max (1 : ℝ) M))).prod = (max 1 M) ^ P.roots.card
      rw [Multiset.map_const, Multiset.prod_replicate]

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.MonicRoots.Constructions.RootPolynomials
