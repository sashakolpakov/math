import Mathlib.RingTheory.Etale.StandardEtale

/-! # Standard Etale Powers -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.StandardEtalePowers

noncomputable section

/-! Positive powers of the localization polynomial preserve the actual standard etale algebra. -/

open _root_.Polynomial

universe u

variable {R : Type u} [CommRing R] (P Q : StandardEtalePair R) (n : ℕ)
  (hf : Q.f = P.f) (hg : Q.g = P.g ^ (n + 1))

include hf hg in
theorem forward_hasMap : Q.HasMap P.X := by
  constructor
  · rw [hf]
    exact P.hasMap_X.1
  · rw [hg, map_pow]
    exact P.hasMap_X.2.pow (n + 1)

include hf hg in
theorem backward_hasMap : P.HasMap Q.X := by
  constructor
  · rw [← hf]
    exact Q.hasMap_X.1
  · apply (isUnit_pow_succ_iff).mp
    rw [← map_pow, ← hg]
    exact Q.hasMap_X.2

def equiv : Q.Ring ≃ₐ[R] P.Ring :=
  AlgEquiv.ofAlgHom (Q.lift P.X (forward_hasMap P Q n hf hg))
    (P.lift Q.X (backward_hasMap P Q n hf hg))
    (P.hom_ext (by simp only [AlgHom.comp_apply, StandardEtalePair.lift_X, AlgHom.id_apply]))
    (Q.hom_ext (by simp only [AlgHom.comp_apply, StandardEtalePair.lift_X, AlgHom.id_apply]))

theorem equiv_X : equiv P Q n hf hg Q.X = P.X :=
  Q.lift_X P.X (forward_hasMap P Q n hf hg)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.StandardEtalePowers
