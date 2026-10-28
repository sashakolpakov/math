import Mathlib

/-! # Parameter Uniqueness -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ParameterUniqueness.Central

noncomputable section

/-! The normalized triple is unique up to permutation, retaining repeated
roots. The finite-family matching uses equal fiber cardinalities. -/

open scoped Classical BigOperators

theorem finite_family_permutation {I F : Type*} [Fintype I]
    (α β : I → F) (h : Finset.univ.val.map α = Finset.univ.val.map β) :
    ∃ σ : Equiv.Perm I, ∀ i, α i = β (σ i) := by
  have hc (z : F) : Fintype.card {i // α i = z} = Fintype.card {i // β i = z} := by
    have hz := congrArg (Multiset.count z) h
    simpa only [Multiset.count_map, Fintype.card_subtype, Finset.card_def,
      Finset.filter_val, eq_comm] using hz
  let e : ∀ z, {i // α i = z} ≃ {i // β i = z} := fun z => Fintype.equivOfCardEq (hc z)
  exact ⟨Equiv.ofFiberEquiv e, fun i => (Equiv.ofFiberEquiv_map e i).symm⟩

theorem parameter_triple_unique {F : Type*} [Field F] (α β : Fin 3 → F)
    (hs : α 0 + α 1 + α 2 = β 0 + β 1 + β 2)
    (hp : α 0 * α 1 + α 0 * α 2 + α 1 * α 2 =
      β 0 * β 1 + β 0 * β 2 + β 1 * β 2)
    (hd : α 0 * α 1 * α 2 = β 0 * β 1 * β 2) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ i, α i = β (σ i) := by
  let P (a : Fin 3 → F) : Polynomial F := ∏ i : Fin 3, (Polynomial.X - Polynomial.C (a i))
  have hP (a : Fin 3 → F) : P a = Polynomial.X ^ 3 -
      Polynomial.C (a 0 + a 1 + a 2) * Polynomial.X ^ 2 +
      Polynomial.C (a 0 * a 1 + a 0 * a 2 + a 1 * a 2) * Polynomial.X -
      Polynomial.C (a 0 * a 1 * a 2) := by
    simp only [P, Fin.prod_univ_three, map_add, map_mul]
    ring
  have he : P α = P β := by rw [hP, hP, hs, hp, hd]
  have hr (a : Fin 3 → F) : (P a).roots = Finset.univ.val.map a := by
    have hprod : ((Finset.univ.val.map a).map (fun x => Polynomial.X - Polynomial.C x)).prod = P a := by
      rw [Multiset.map_map]
      rfl
    rw [← hprod, Polynomial.roots_multiset_prod_X_sub_C]
  apply finite_family_permutation α β
  rw [← hr, ← hr, he]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ParameterUniqueness.Central
