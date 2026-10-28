import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Ring Quotient Factor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RingQuotientFactor

/-! A factor between two surjective ring quotients with the same kernel is bijective. -/

universe u v w

variable {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [CommRing T]
  (q : R →+* S) (h : R →+* T) (g : S →+* T)
  (hq : Function.Surjective q) (hh : Function.Surjective h)
  (hc : g.comp q = h) (hk : RingHom.ker q = RingHom.ker h)

include hq hh hc hk in
theorem bijective : Function.Bijective g := by
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := hq a
    obtain ⟨y, rfl⟩ := hq b
    have he : h x = h y :=
      (RingHom.congr_fun hc x).symm.trans (hab.trans (RingHom.congr_fun hc y))
    have hm : x - y ∈ RingHom.ker h := by
      change h (x - y) = 0
      rw [map_sub, he, sub_self]
    have hq0 : x - y ∈ RingHom.ker q := hk.symm ▸ hm
    exact sub_eq_zero.mp ((q.map_sub x y).symm.trans hq0)
  · intro t
    obtain ⟨r, hr⟩ := hh t
    exact ⟨q r, (RingHom.congr_fun hc r).trans hr⟩

end OAI.NumberTheory.PadicHodge.IntegralComparison.RingQuotientFactor
