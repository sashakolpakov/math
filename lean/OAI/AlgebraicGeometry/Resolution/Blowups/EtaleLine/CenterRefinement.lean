import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.RetractionStep

/-! # Center Refinement -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.CenterRefinement.Construction

noncomputable section

/-! The actual normal-plus-coefficient center commutes with compatible line refinements. -/

universe u

theorem etaleLineCenter_map_of_compatible_maps {H B R V : Type u}
    [CommRing H] [CommRing B] [CommRing R] [CommRing V]
    [Algebra (Polynomial H) R] [Algebra (Polynomial B) V]
    (K : Ideal H) (φ : H →+* B) (f : R →+* V)
    (hcoeff : ∀ h : H, f (Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap (R := R) h) =
      Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap (R := V) (φ h))
    (hcoord : f (algebraMap (Polynomial H) R Polynomial.X) =
      algebraMap (Polynomial B) V Polynomial.X) :
    (Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K).map f = Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := V) (K.map φ) := by
  have hc : f.comp (Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap (H := H) (R := R)) =
      (Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap (H := B) (R := V)).comp φ := RingHom.ext hcoeff
  rw [RetractionStep.Construction.etaleLineCenter_eq, Ideal.map_sup, Ideal.map_map, Ideal.map_span, Set.image_singleton,
    hcoord, hc, RetractionStep.Construction.etaleLineCenter_eq, Ideal.map_map]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.CenterRefinement.Construction
