import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.QuotientNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.CenterDescent

/-! # Center Descent -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.CenterDescent.Construction

noncomputable section

/-! Equality of hypersurface centers reflects equality of their ambient ideals. -/

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The square of ambient and aligned hypersurface maps commutes on every ideal. -/
theorem alignedHypersurfaceMap_ideal_map (f : R →+* S) (z : R) (w : S)
    (h : f z = w) (I : Ideal R) :
    (I.map (Ideal.Quotient.mk (Ideal.span {z}))).map (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap f z w h) =
      (I.map f).map (Ideal.Quotient.mk (Ideal.span {w})) := by
  rw [Ideal.map_map, Ideal.map_map]
  rfl

/-- A closed center containing the hypersurface is recovered from its
quotient ideal. Consequently, equality of the compared hypersurface centers
implies equality of the actual ambient center ideals on the common chart. -/
theorem aligned_hypersurface_center_equality (f g : R →+* S) (z t : R)
    (heq : f z = g t) (I L : Ideal R) (hzI : z ∈ I) (htL : t ∈ L)
    (h : (I.map (Ideal.Quotient.mk (Ideal.span {z}))).map
          (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap f z (f z) rfl) =
        (L.map (Ideal.Quotient.mk (Ideal.span {t}))).map
          (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap g t (f z) heq.symm)) : I.map f = L.map g := by
  rw [alignedHypersurfaceMap_ideal_map, alignedHypersurfaceMap_ideal_map] at h
  have hI : Ideal.span {f z} ≤ I.map f :=
    (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem f hzI)
  have hL : Ideal.span {f z} ≤ L.map g := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    rw [heq]
    exact Ideal.mem_map_of_mem g htL
  have he := (Ideal.map_eq_iff_sup_ker_eq_of_surjective
    (Ideal.Quotient.mk (Ideal.span {f z})) Ideal.Quotient.mk_surjective).mp h
  rw [Ideal.mk_ker, sup_eq_left.mpr hI, sup_eq_left.mpr hL] at he
  exact he

variable {k C : Type u} [CommRing k] [Field C]
  [Algebra k R] [Algebra k S] [Algebra k C]

/-- Compatible hypersurface centers descend to the same center on an
actual neighborhood of the original point, provided the comparison preserves
the second permissible ambient center. -/
theorem pointed_hypersurface_center_descent (f g : R →ₐ[k] S)
    (hf : f.toRingHom.Etale) (v : S →ₐ[k] C) (r : R →ₐ[k] C)
    (hv : ∀ x : R, v (f x) = r x) (z t : R) (heq : f z = g t)
    (I L : Ideal R) (hzI : z ∈ I) (htL : t ∈ L) (hI : I.FG) (hL : L.FG)
    (h : (I.map (Ideal.Quotient.mk (Ideal.span {z}))).map
          (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap f.toRingHom z (f z) rfl) =
        (L.map (Ideal.Quotient.mk (Ideal.span {t}))).map
          (Blowups.Etale.QuotientNaturality.Construction.alignedHypersurfaceMap g.toRingHom t (f z) heq.symm))
    (hpreserve : L.map f.toRingHom = L.map g.toRingHom) :
    ∃ s : R, r s ≠ 0 ∧ I.map (algebraMap R (Localization.Away s)) =
      L.map (algebraMap R (Localization.Away s)) :=
  Blowups.Etale.CenterDescent.Construction.pointed_etale_center_equality_neighborhood f g hf v r hv I L hI hL
    (aligned_hypersurface_center_equality f.toRingHom g.toRingHom z t heq I L hzI htL h)
    hpreserve

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.CenterDescent.Construction
