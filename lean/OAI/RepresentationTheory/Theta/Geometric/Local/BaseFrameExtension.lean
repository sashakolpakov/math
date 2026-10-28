import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionTriviality

/-! # Base Frame Extension -/

namespace OAI.RepresentationTheory.Theta.Geometric.Local.BaseFrameExtension

noncomputable section

/-! Over a local base, a section of a proper line-bundle family that
is a frame on the closed fiber is a frame everywhere. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of R)) [IsProper π]
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (s : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf)

theorem section_isIso_of_closedFiber_frame
    (h : IsIso (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection (π.fiberι (IsLocalRing.closedPoint R)) s)) : IsIso s := by
  have htop : AlgebraicGeometry.Quotients.FiniteDescent.SectionTriviality.Construction.SectionTrivialityOpen.baseOpen π L s = ⊤ :=
    (IsLocalRing.closedPoint_mem_iff _).mp
      ((AlgebraicGeometry.Quotients.FiniteDescent.SectionTriviality.Construction.SectionTrivialityOpen.mem_iff π L s _).mpr h)
  apply (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames.isIso_iff_sectionNonvanishing_eq_top s).mpr
  apply top_unique
  intro x _
  have hx : π x ∈ AlgebraicGeometry.Quotients.FiniteDescent.SectionTriviality.Construction.SectionTrivialityOpen.baseOpen π L s := by
    rw [htop]
    trivial
  by_contra hzero
  exact hx ⟨x, hzero, rfl⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Local.BaseFrameExtension
