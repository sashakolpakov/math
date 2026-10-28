import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SourcePropertyOpenLocus
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Source Property Base Open -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.SourcePropertyBaseOpen

noncomputable section

/-! For a proper family, removing the image of the complement of a local source-property locus gives an actual open base carrying that property. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]

def properSourcePropertyBaseOpen : S.Opens :=
  ⟨(f '' (SourcePropertyOpenLocus.sourcePropertyOpenLocus P f : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ (SourcePropertyOpenLocus.sourcePropertyOpenLocus P f).isOpen.isClosed_compl).isOpen_compl⟩

omit [IsZariskiLocalAtSource P] in
theorem properSourcePropertyBaseOpen_preimage :
    f ⁻¹ᵁ properSourcePropertyBaseOpen P f ≤ SourcePropertyOpenLocus.sourcePropertyOpenLocus P f := by
  intro x hx
  by_contra h
  exact hx ⟨x, h, rfl⟩

theorem properSourcePropertyBaseOpen_restrict [P.IsStableUnderBaseChange] :
    P (f ∣_ properSourcePropertyBaseOpen P f) := by
  have hs : P ((f ⁻¹ᵁ properSourcePropertyBaseOpen P f).ι ≫ f) :=
    (SourcePropertyOpenLocus.sourcePropertyOpenLocus_iff P f _).mpr (properSourcePropertyBaseOpen_preimage P f)
  have hc : P ((f ∣_ properSourcePropertyBaseOpen P f) ≫ (properSourcePropertyBaseOpen P f).ι) := by
    rw [morphismRestrict_ι]
    exact hs
  have hpb : IsPullback (𝟙 (f ⁻¹ᵁ properSourcePropertyBaseOpen P f).toScheme)
      (f ∣_ properSourcePropertyBaseOpen P f)
      ((f ∣_ properSourcePropertyBaseOpen P f) ≫ (properSourcePropertyBaseOpen P f).ι)
      (properSourcePropertyBaseOpen P f).ι :=
    IsPullback.of_horiz_isIso_mono ⟨Category.id_comp _⟩
  exact MorphismProperty.of_isPullback (P := P) hpb hc

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.SourcePropertyBaseOpen
