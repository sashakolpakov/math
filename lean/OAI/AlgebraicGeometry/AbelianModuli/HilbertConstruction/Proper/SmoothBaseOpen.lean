import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.OpenSourceCriterion
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Smooth Base Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.SmoothBaseOpen

noncomputable section

/-! Removing the proper image of the nonsmooth locus gives an actual open base over which the whole family is smooth. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [LocallyOfFinitePresentation f]

def properSmoothBaseOpen : S.Opens :=
  ⟨(f '' (f.smoothLocus : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ f.smoothLocus.isOpen.isClosed_compl).isOpen_compl⟩

theorem properSmoothBaseOpen_preimage : f ⁻¹ᵁ properSmoothBaseOpen f ≤ f.smoothLocus := by
  intro x hx
  by_contra h
  exact hx ⟨x, h, rfl⟩

theorem properSmoothBaseOpen_restrict_smooth : Smooth (f ∣_ properSmoothBaseOpen f) := by
  have hs : Smooth ((f ⁻¹ᵁ properSmoothBaseOpen f).ι ≫ f) :=
    HilbertConstruction.Smooth.OpenSourceCriterion.smooth_open_source_of_le_smoothLocus f _ (properSmoothBaseOpen_preimage f)
  have hc : Smooth ((f ∣_ properSmoothBaseOpen f) ≫ (properSmoothBaseOpen f).ι) := by
    rw [morphismRestrict_ι]
    exact hs
  have hpb : IsPullback (𝟙 (f ⁻¹ᵁ properSmoothBaseOpen f).toScheme)
      (f ∣_ properSmoothBaseOpen f)
      ((f ∣_ properSmoothBaseOpen f) ≫ (properSmoothBaseOpen f).ι) (properSmoothBaseOpen f).ι :=
    IsPullback.of_horiz_isIso_mono ⟨Category.id_comp _⟩
  exact MorphismProperty.of_isPullback (P := @Smooth) hpb hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.SmoothBaseOpen
