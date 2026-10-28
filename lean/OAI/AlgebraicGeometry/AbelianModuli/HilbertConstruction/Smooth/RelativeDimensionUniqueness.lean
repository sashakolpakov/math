import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.RelativeDimensionRingUniqueness
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties

/-! # Relative Dimension Uniqueness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.RelativeDimensionUniqueness

noncomputable section

/-! A nonempty scheme morphism has at most one smooth relative dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem smoothRelativeDimension_unique {X S : Scheme.{u}} (f : X ⟶ S) (n m : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension m f] (x : X) : n = m := by
  obtain ⟨U, hU, V, hV, hx, e, _⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  exact RelativeDimensionRingUniqueness.locallyStandardSmoothRelativeDimension_unique (f.appLE U V e).hom n m
    (HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension n) f inferInstance ⟨U, hU⟩ ⟨V, hV⟩ e)
    (HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension m) f inferInstance ⟨U, hU⟩ ⟨V, hV⟩ e)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.RelativeDimensionUniqueness
