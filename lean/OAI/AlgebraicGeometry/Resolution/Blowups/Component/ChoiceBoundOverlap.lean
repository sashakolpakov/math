import OAI.AlgebraicGeometry.Resolution.Blowups.Component.ChoiceBoundNaturality

/-! # Choice Bound Overlap -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Component

noncomputable section

/-! Bounds transfer between complete chart choices on an actual common étale refinement. -/

universe u

theorem CenterChoice.Construction.ComponentCenterChoice.hasBound_on_common_refinement
    {k R A S : Type u} [Field k] [CommRing R] [CommRing A] [CommRing S]
    [Algebra k R] [Algebra k A] [Algebra k S] [Algebra ℚ R]
    [Algebra.Smooth k R] [Algebra.Smooth k A]
    (f : R →ₐ[k] S) (g : A →ₐ[k] S) (hf : f.toRingHom.Etale) (hg : g.toRingHom.Etale)
    {J : Ideal R} {L : Ideal A} (hJL : J.map f.toRingHom = L.map g.toRingHom)
    {n m : ℕ} (C : CenterChoice.Construction.ComponentCenterChoice k R J n) (B : CenterChoice.Construction.ComponentCenterChoice k A L n)
    (hb : C.HasBound m) : (B.mapEtale g hg).HasBound m := by
  cases C with
  | terminal ht =>
      apply (B.mapEtale g hg).hasBound_of_terminal
      rw [← hJL, ← Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k f hf, ht, Ideal.map_top]
  | normal z D hD hz =>
      cases B with
      | terminal _ => trivial
      | normal t E hE ht =>
          exact Coefficient.BoundOverlap.Construction.coefficient_bound_on_common_refinement k f g hf hg J L hJL n m z t D E hD hE hz ht hb

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Component
