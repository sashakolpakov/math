import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.DimensionLocalCharts

/-! # Dimension Cartesian Reflection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.DimensionCartesianReflection

noncomputable section

/-! For a smooth original family, a fixed smooth dimension on a Cartesian base change reflects to the original source at every point hit by that base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

local instance dimensionReflectionSourceLocal (g : ℕ) :
    IsZariskiLocalAtSource (@SmoothOfRelativeDimension g : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g))

theorem smoothDimension_cartesian_source_mem
    {X Y S T : Scheme.{u}} (q : Y ⟶ X) (p : Y ⟶ T) (f : X ⟶ S) (c : T ⟶ S)
    (h : IsPullback q p f c) [Smooth f] (g : ℕ) [SmoothOfRelativeDimension g p] (y : Y) :
    q y ∈ Proper.SmoothDimensionOpen.smoothDimensionSourceOpen f g := by
  obtain ⟨n, V, hy, hn⟩ := DimensionLocalCharts.smooth_exists_sourceOpen_relativeDimension f (q y)
  let W := q ⁻¹ᵁ V
  have hpb : IsPullback (q ∣_ V) (W.ι ≫ p) (V.ι ≫ f) c :=
    (isPullback_morphismRestrict q V).paste_vert h
  have : SmoothOfRelativeDimension n (W.ι ≫ p) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback hpb hn
  have : SmoothOfRelativeDimension g (W.ι ≫ p) :=
    IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension g) inferInstance W.ι
  have hng : n = g := RelativeDimensionUniqueness.smoothRelativeDimension_unique (W.ι ≫ p) n g ⟨y, hy⟩
  subst n
  exact (Proper.SmoothDimensionOpen.smoothDimensionSourceOpen_iff f g V).mp hn hy

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.DimensionCartesianReflection
