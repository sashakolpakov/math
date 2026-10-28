import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionBase
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Section Triviality -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionTriviality.Construction.SectionTrivialityOpen

noncomputable section

/-! For a fixed section of a line bundle in a proper family, the fibers on
which that section is a frame form an open subset of the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
variable (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf)

/-- Exclude the proper image of the zero locus of the chosen section. -/
def baseOpen : S.Opens :=
  ⟨(f '' (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s).isOpen.isClosed_compl).isOpen_compl⟩

theorem mem_iff (y : S) :
    y ∈ baseOpen f L s ↔ IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (f.fiberι y) s) := by
  rw [AbelianModuli.HilbertConstruction.Section.Frames.isIso_iff_sectionNonvanishing_eq_top, SectionBase.Construction.SectionBaseChange.nonvanishing_pullback]
  constructor
  · intro hy
    apply top_unique
    intro x _
    change f.fiberι y x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s
    by_contra hx
    apply hy
    refine ⟨f.fiberι y x, hx, ?_⟩
    have h := (Set.ext_iff.mp (f.range_fiberι y) _).mp (Set.mem_range_self x)
    exact h
  · intro h
    rintro ⟨x, hx, hxy⟩
    have hr : x ∈ Set.range (f.fiberι y) := by
      rw [f.range_fiberι y]
      exact hxy
    obtain ⟨z, rfl⟩ := hr
    have hz : z ∈ f.fiberι y ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s := by rw [h]; trivial
    exact hx hz

theorem isIso_restrict : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (f ⁻¹ᵁ baseOpen f L s).ι s) := by
  apply (AbelianModuli.HilbertConstruction.Section.Frames.isIso_iff_sectionNonvanishing_eq_top _).mpr
  rw [SectionBase.Construction.SectionBaseChange.nonvanishing_pullback]
  apply top_unique
  intro x _
  change x.1 ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s
  by_contra hx
  exact x.2 ⟨x.1, hx, rfl⟩

/-- Once a fiberwise frame has been lifted to a global section, properness
extends that frame over a neighborhood of the fiber. -/
theorem exists_open (y : S) (hy : IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (f.fiberι y) s)) :
    ∃ V : S.Opens, y ∈ V ∧ IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (f ⁻¹ᵁ V).ι s) :=
  ⟨baseOpen f L s, (mem_iff f L s y).mpr hy, isIso_restrict f L s⟩

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionTriviality.Construction.SectionTrivialityOpen
