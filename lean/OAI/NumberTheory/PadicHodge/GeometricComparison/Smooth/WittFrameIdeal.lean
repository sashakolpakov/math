import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing

/-! # Witt Frame Ideal -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.WittFrameIdeal.SmoothWittFrameIdeal

noncomputable section

/-! The actual defining ideal of a truncated flat Witt frame is generated
by the image of the original prime. -/

universe u
variable (p : ℕ) (A : Type u) [CommRing A] (n : ℕ)

theorem eq_span : IntegralComparison.SmoothWitt.FrameRing.ideal p A n =
    Ideal.span {(p : IntegralComparison.SmoothWitt.FrameRing.Ring p A n)} := by
  change (Ideal.span {(p : A)}).map (Ideal.Quotient.mk _) = _
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.WittFrameIdeal.SmoothWittFrameIdeal
