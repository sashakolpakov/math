import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionTriviality
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Section Frame Base Change -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SectionFrameBaseChange.Construction

noncomputable section

/-! The open subset where a section is a frame represents that condition
under every base change, including non-flat and nonreduced test schemes. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

theorem pullbackSection_isIso_iff_baseOpen
    {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
    [IsProper π] (hp : IsPullback f ρ π g) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf) :
    IsIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f s) ↔ ∀ y : T, g y ∈ Quotients.FiniteDescent.SectionTriviality.Construction.SectionTrivialityOpen.baseOpen π L s := by
  rw [AbelianModuli.HilbertConstruction.Section.Frames.isIso_iff_sectionNonvanishing_eq_top, Quotients.FiniteDescent.SectionBase.Construction.SectionBaseChange.nonvanishing_pullback]
  constructor
  · intro h y
    rintro ⟨x, hx, hxy⟩
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback hp x y hxy
    have hmem : f z ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s := by
      change z ∈ f ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s
      rw [h]
      trivial
    exact hx (hz ▸ hmem)
  · intro h
    apply top_unique
    intro y _
    change f y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s
    by_contra hy
    apply h (ρ y)
    exact ⟨f y, hy, congrArg (fun k : Y ⟶ S => k y) hp.w⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SectionFrameBaseChange.Construction
