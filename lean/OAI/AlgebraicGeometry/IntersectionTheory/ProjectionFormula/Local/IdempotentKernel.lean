import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-! # Idempotent Kernel -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.IdempotentKernel

noncomputable section

/-! A proper ideal in a Noetherian local ring cannot retain a nonzero
idempotent quotient. Applied after a surjection, this identifies the
localized inverse-image ideal with the localized kernel. -/

universe u v w

variable (R : Type u) (S : Type v) (L : Type w) [CommRing R] [CommRing S] [CommRing L]

theorem global_containment (φ : R →+* S) (hφ : Function.Surjective φ)
    (I : Ideal S) (hI : I * I = I) :
    I.comap φ ≤ RingHom.ker φ ⊔ (I.comap φ) * (I.comap φ) := by
  have hk : RingHom.ker φ ≤ I.comap φ := Ideal.comap_mono bot_le
  have he : ((I.comap φ) * (I.comap φ)).map φ = (I.comap φ).map φ := by
    rw [Ideal.map_mul, Ideal.map_comap_of_surjective φ hφ, hI]
  have hc := congrArg (Ideal.comap φ) he
  rw [Ideal.comap_map_of_surjective', Ideal.comap_map_of_surjective', sup_of_le_left hk] at hc
  · exact le_of_eq (hc.symm.trans (sup_comm _ _))
  all_goals exact hφ

theorem localized [IsNoetherianRing L] [IsLocalRing L]
    (φ : R →+* S) (hφ : Function.Surjective φ) (I : Ideal S) (hI : I * I = I)
    (g : R →+* L) (hp : (I.comap φ).map g ≠ ⊤) :
    (I.comap φ).map g = (RingHom.ker φ).map g := by
  let J := (I.comap φ).map g
  let K := (RingHom.ker φ).map g
  have hK : K ≤ J := Ideal.map_mono (Ideal.comap_mono bot_le)
  have hj : J ≤ K ⊔ J * J := by
    have h := Ideal.map_mono (global_containment R S φ hφ I hI) (f := g)
    simpa only [Ideal.map_sup, Ideal.map_mul] using h
  apply le_antisymm _ hK
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian J)
    ((IsLocalRing.le_maximalIdeal hp).trans (IsLocalRing.maximalIdeal_le_jacobson _))
  simpa only [Ideal.smul_eq_mul] using hj

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.IdempotentKernel
