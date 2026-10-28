import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.DimensionCartesianReflection
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Smooth Dimension Classification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.SmoothDimensionClassification

noncomputable section

/-! For a proper smooth family, the maximal dimension-g open classifies exactly the base changes that are smooth of relative dimension g, on all test schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X S T : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] (g : ℕ) (c : T ⟶ S)

theorem smoothDimension_pullback_range_subset [SmoothOfRelativeDimension g (pullback.snd f c)] :
    Set.range c ⊆ SmoothDimensionOpen.properSmoothDimensionBaseOpen f g := by
  rintro s ⟨t, rfl⟩ ⟨x, hx, hxt⟩
  obtain ⟨y, hy, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := c) x t hxt
  have hm := HilbertConstruction.Smooth.DimensionCartesianReflection.smoothDimension_cartesian_source_mem (pullback.fst f c) (pullback.snd f c)
    f c (IsPullback.of_hasPullback f c) g y
  rw [hy] at hm
  exact hx hm

theorem smoothDimension_pullback_iff_range_subset :
    SmoothOfRelativeDimension g (pullback.snd f c) ↔ Set.range c ⊆ SmoothDimensionOpen.properSmoothDimensionBaseOpen f g := by
  constructor
  · intro h
    let : SmoothOfRelativeDimension g (pullback.snd f c) := h
    exact smoothDimension_pullback_range_subset f g c
  · exact SmoothDimensionOpen.smoothDimension_pullback_of_range_subset f g c

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.SmoothDimensionClassification
