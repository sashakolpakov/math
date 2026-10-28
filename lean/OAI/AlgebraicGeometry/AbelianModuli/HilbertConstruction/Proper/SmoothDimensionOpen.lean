import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.PropertyOpenMaximality

/-! # Smooth Dimension Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.SmoothDimensionOpen

noncomputable section

/-! A proper family has an actual maximal open base on which it is smooth of a specified relative dimension; every test scheme mapping into that open inherits the fixed dimension. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

local instance smoothDimensionSourceLocal (g : ℕ) :
    IsZariskiLocalAtSource (@SmoothOfRelativeDimension g : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g))

local instance smoothDimensionOpenPostcomp (g : ℕ) :
    MorphismProperty.RespectsRight (@SmoothOfRelativeDimension g : MorphismProperty Scheme.{u}) @IsOpenImmersion where
  postcomp i hi f hf := by
    have : IsOpenImmersion i := hi
    have : SmoothOfRelativeDimension g f := hf
    have h : SmoothOfRelativeDimension (g + 0) (f ≫ i) := smoothOfRelativeDimension_comp g 0 f i
    simpa only [Nat.add_zero] using h

variable {X S : Scheme.{u}} (f : X ⟶ S) (g : ℕ)

def smoothDimensionSourceOpen : X.Opens := SourcePropertyOpenLocus.sourcePropertyOpenLocus (@SmoothOfRelativeDimension g) f

theorem smoothDimensionSourceOpen_property :
    SmoothOfRelativeDimension g ((smoothDimensionSourceOpen f g).ι ≫ f) :=
  SourcePropertyOpenLocus.sourcePropertyOpenLocus_property (@SmoothOfRelativeDimension g) f

theorem smoothDimensionSourceOpen_iff (U : X.Opens) :
    SmoothOfRelativeDimension g (U.ι ≫ f) ↔ U ≤ smoothDimensionSourceOpen f g :=
  SourcePropertyOpenLocus.sourcePropertyOpenLocus_iff (@SmoothOfRelativeDimension g) f U

variable [IsProper f]

def properSmoothDimensionBaseOpen : S.Opens := SourcePropertyBaseOpen.properSourcePropertyBaseOpen (@SmoothOfRelativeDimension g) f

theorem properSmoothDimensionBaseOpen_restrict :
    SmoothOfRelativeDimension g (f ∣_ properSmoothDimensionBaseOpen f g) := by
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension g : MorphismProperty Scheme.{u}) :=
    smoothOfRelativeDimension_isStableUnderBaseChange g
  exact SourcePropertyBaseOpen.properSourcePropertyBaseOpen_restrict (@SmoothOfRelativeDimension g) f

theorem properSmoothDimensionBaseOpen_restrict_iff (U : S.Opens) :
    SmoothOfRelativeDimension g (f ∣_ U) ↔ U ≤ properSmoothDimensionBaseOpen f g := by
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension g : MorphismProperty Scheme.{u}) :=
    smoothOfRelativeDimension_isStableUnderBaseChange g
  exact PropertyOpenMaximality.properSourcePropertyBaseOpen_restrict_iff (@SmoothOfRelativeDimension g) f U

theorem smoothDimension_pullback_of_range_subset {T : Scheme.{u}} (c : T ⟶ S)
    (hc : Set.range c ⊆ properSmoothDimensionBaseOpen f g) :
    SmoothOfRelativeDimension g (pullback.snd f c) := by
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension g : MorphismProperty Scheme.{u}) :=
    smoothOfRelativeDimension_isStableUnderBaseChange g
  exact SourcePropertyOpenRecovery.property_pullback_of_range_subset_properBaseOpen (@SmoothOfRelativeDimension g) f c hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.SmoothDimensionOpen
