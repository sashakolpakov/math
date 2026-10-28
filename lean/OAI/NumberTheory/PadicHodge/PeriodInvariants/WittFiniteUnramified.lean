import OAI.NumberTheory.PadicHodge.PeriodInvariants.WittAlgebraFunctor
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Unramified.Basic

/-! # Witt Finite Unramified -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.WittFiniteUnramified

noncomputable section

/-! # A finite-type Witt algebra of a perfect ring is formally unramified -/

attribute [local instance] WittAlgebraFunctor.wittAlgebra

variable (p : ℕ) [Fact p.Prime] (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [CharP B p] [PerfectRing B p]

theorem teichmuller_mem (b : B) :
    KaehlerDifferential.D (WittVector p A) (WittVector p B) (WittVector.teichmuller p b) ∈
      Ideal.span {(p : WittVector p B)} •
        (⊤ : Submodule (WittVector p B) (KaehlerDifferential (WittVector p A) (WittVector p B))) := by
  obtain ⟨c, hc⟩ := surjective_frobenius B p b
  change c ^ p = b at hc
  rw [← hc, map_pow, Derivation.leibniz_pow]
  have hm := Submodule.smul_mem_smul
    (Ideal.subset_span (Set.mem_singleton (p : WittVector p B)))
    (show (WittVector.teichmuller p c) ^ (p - 1) •
      KaehlerDifferential.D (WittVector p A) (WittVector p B) (WittVector.teichmuller p c) ∈
        (⊤ : Submodule (WittVector p B) (KaehlerDifferential (WittVector p A) (WittVector p B))) from trivial)
  simpa only [Nat.cast_smul_eq_nsmul] using hm

theorem derivation_mem (x : WittVector p B) :
    KaehlerDifferential.D (WittVector p A) (WittVector p B) x ∈ Ideal.span {(p : WittVector p B)} •
      (⊤ : Submodule (WittVector p B) (KaehlerDifferential (WittVector p A) (WittVector p B))) := by
  have hz : (x - WittVector.teichmuller p (x.coeff 0)).coeff 0 = 0 := by
    change WittVector.constantCoeff (x - WittVector.teichmuller p (x.coeff 0)) = 0
    rw [map_sub]
    exact sub_self _
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp
    ((WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr hz)
  have he : x = WittVector.teichmuller p (x.coeff 0) + (p : WittVector p B) * y := by
    rw [← hy]
    abel
  rw [he, map_add, Derivation.leibniz, Derivation.map_natCast, smul_zero, add_zero]
  exact Submodule.add_mem _ (teichmuller_mem p A B (x.coeff 0))
    (Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton _)) Submodule.mem_top)

theorem unramified [Algebra.FiniteType (WittVector p A) (WittVector p B)] :
    Algebra.FormallyUnramified (WittVector p A) (WittVector p B) := by
  let W := WittVector p B
  let Ω := KaehlerDifferential (WittVector p A) W
  let I : Ideal W := Ideal.span {(p : W)}
  have hle : (⊤ : Submodule W Ω) ≤ I • ⊤ := by
    rw [← KaehlerDifferential.span_range_derivation (WittVector p A) W]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    rw [KaehlerDifferential.span_range_derivation]
    exact derivation_mem p A B x
  have he : (⊤ : Submodule W Ω) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I ⊤ Module.Finite.fg_top hle
      (IsAdicComplete.le_jacobson_bot I)
  have : Subsingleton Ω := ⟨fun x y => by
    have hx : x ∈ (⊥ : Submodule W Ω) := he ▸ Submodule.mem_top
    have hy : y ∈ (⊥ : Submodule W Ω) := he ▸ Submodule.mem_top
    have hx0 : x = 0 := by simpa only [Submodule.mem_bot] using hx
    have hy0 : y = 0 := by simpa only [Submodule.mem_bot] using hy
    exact hx0.trans hy0.symm⟩
  exact ⟨this⟩

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.WittFiniteUnramified
