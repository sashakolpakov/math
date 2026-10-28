import Mathlib.RingTheory.Flat.LocallyFree

/-! # Quotient Rank Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.QuotientRankDetection

noncomputable section

/-! An inclusion of relation submodules is an equality when their finite flat quotients have the same ranks. -/

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

theorem submodule_eq_of_flat_quotient_ranks (p q : Submodule R M) (hpq : p ≤ q)
    [Module.Finite R (M ⧸ p)] [Module.Flat R (M ⧸ p)]
    [Module.Finite R (M ⧸ q)] [Module.Flat R (M ⧸ q)]
    (hr : ∀ x : PrimeSpectrum R, Module.rankAtStalk (R := R) (M ⧸ p) x =
      Module.rankAtStalk (R := R) (M ⧸ q) x) : p = q := by
  have hb := Module.bijective_of_surjective_of_rankAtStalk_eq (Submodule.factor_surjective hpq)
    (fun m _ => hr ⟨m, inferInstance⟩)
  apply le_antisymm hpq
  intro x hx
  have hq : q.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero q).mpr hx
  have hp : p.mkQ x = 0 := by
    apply hb.injective
    rw [Submodule.factor_mk, map_zero, hq]
  exact (Submodule.Quotient.mk_eq_zero p).mp hp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.QuotientRankDetection
