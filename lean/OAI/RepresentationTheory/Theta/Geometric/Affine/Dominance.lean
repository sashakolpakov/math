import OAI.RepresentationTheory.Theta.Geometric.AffineChartSectionCoordinates
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Dominance -/

namespace OAI.RepresentationTheory.Theta.Geometric.Affine.Dominance

noncomputable section

/-! An injected affine coordinate algebra gives an injective structure
sheaf map on every open subset. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem specMap_schemeTheoreticallyDominant {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) :
    IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom f)) := by
  constructor
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.Hom.ker_apply]
  change RingHom.ker (Spec.map (CommRingCat.ofHom f)).appTop.hom = ⊥
  exact (RingHom.injective_iff_ker_eq_bot _).mp (AffineChartSectionCoordinates.specMap_appTop_injective f hf)

end

end OAI.RepresentationTheory.Theta.Geometric.Affine.Dominance
