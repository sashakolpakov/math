import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StandardSmoothDomainReduced
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-! # Domain Reduced -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.DomainReduced

noncomputable section

/-! Smooth algebras over domains are reduced, by a standard smooth basic-open cover. -/

universe u v

theorem smooth_domain_isReduced (R : Type u) (S : Type v)
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [Algebra.Smooth R S] :
    IsReduced S := by
  obtain ⟨s, hs, h⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth R S
  have (x : s) : IsReduced (Localization.Away x.val) := by
    have := h x.val x.property
    exact StandardSmoothDomainReduced.standardSmooth_domain_isReduced R (Localization.Away x.val)
  exact isReduced_of_injective (algebraMap S (Π x : s, Localization.Away x.val))
    (Localization.algebraMap_injective_of_span_eq_top s hs)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.DomainReduced
