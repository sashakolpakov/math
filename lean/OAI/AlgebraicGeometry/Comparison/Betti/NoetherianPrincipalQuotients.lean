import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span

/-! # Noetherian Principal Quotients -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.NoetherianPrincipalQuotients.AnalyticLocal

noncomputable section

/-! Noetherianity reduces to quotients by nonzero principal ideals. -/

theorem noetherian_of_nonzero_principal_quotients (R : Type*) [CommRing R]
    (h : ∀ a : R, a ≠ 0 → IsNoetherianRing (R ⧸ Ideal.span {a})) : IsNoetherianRing R := by
  apply (isNoetherianRing_iff_ideal_fg R).mpr
  intro I
  by_cases hI : I = ⊥
  · rw [hI]
    exact Submodule.fg_bot
  · obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    let J : Ideal R := Ideal.span {a}
    let : IsNoetherianRing (R ⧸ J) := h a ha
    have hmap : (I.map (Ideal.Quotient.mk J)).FG := Ideal.fg_of_isNoetherianRing _
    have hker : (I ⊓ RingHom.ker (Ideal.Quotient.mk J)).FG := by
      rw [Ideal.mk_ker, inf_eq_right.mpr ((Ideal.span_singleton_le_iff_mem I).mpr haI)]
      exact Submodule.fg_span_singleton a
    exact Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective hmap hker Ideal.Quotient.mk_surjective

theorem principal_quotient_noetherian_of_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (a : R) [IsNoetherianRing (S ⧸ Ideal.span {e a})] :
    IsNoetherianRing (R ⧸ Ideal.span {a}) := by
  let q := Ideal.quotientEquiv (Ideal.span {a}) (Ideal.span {e a}) e
    (by rw [Ideal.map_span, Set.image_singleton]; rfl)
  exact isNoetherianRing_of_ringEquiv _ q.symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.NoetherianPrincipalQuotients.AnalyticLocal
