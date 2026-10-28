import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks

/-! # Lie Rank Uniqueness -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LieRankUniqueness.CM

noncomputable section

/-! The PEL Lie rank is unique because both coordinate systems preserve
the original addition and dual-number scalar maps. -/

variable {k O : Type} [Field k] [CommRing O] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (AlgebraicGeometry.Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (τ : O →+* k)

theorem rank_unique {d r : ℕ} (hd : AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A ρ τ d)
    (hr : AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A ρ τ r) : d = r := by
  obtain ⟨e, ea, es⟩ := hd
  obtain ⟨f, fa, fs⟩ := hr
  let u : (Fin d → k) ≃ₗ[k] (Fin r → k) := {
    toEquiv := e.trans f.symm
    map_add' := fun x y => by
      apply f.injective
      apply Subtype.ext
      change (f (f.symm (e (x + y)))).val = (f (f.symm (e x) + f.symm (e y))).val
      rw [f.apply_symm_apply, ea, fa, f.apply_symm_apply, f.apply_symm_apply]
    map_smul' := fun a x => by
      apply f.injective
      apply Subtype.ext
      change (f (f.symm (e (a • x)))).val = (f (a • f.symm (e x))).val
      rw [f.apply_symm_apply, es, fs, f.apply_symm_apply] }
  simpa using u.finrank_eq

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LieRankUniqueness.CM
