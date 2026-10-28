import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroSections
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Line Bundle Section Dimension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.LineBundleSectionDimension

noncomputable section

/-! A line bundle with a section nonvanishing at a point has a positive-dimensional space of global sections whenever that space is finite-dimensional. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem lineBundle_sections_finrank_pos_of_nonvanishing
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (L : Line.Bundles.LineBundle X) (s : Line.Bundles.structureModule X ⟶ L.sheaf) (x : X)
    (hx : x ∈ Ample.LineBundles.sectionNonvanishing s)
    [Module.Finite K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj L.sheaf)] :
    0 < Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj L.sheaf) := by
  let z : (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj L.sheaf := Global.Sections.moduleSectionHomEquiv L.sheaf s
  have hz0 : Global.Sections.moduleSectionHomEquiv L.sheaf (0 : Line.Bundles.structureModule X ⟶ L.sheaf) = 0 := rfl
  have hz : z ≠ 0 := by
    intro h
    have hs : s = 0 := (Global.Sections.moduleSectionHomEquiv L.sheaf).injective (h.trans hz0.symm)
    rw [hs, L.sectionNonvanishing_zero] at hx
    exact hx
  have : Nontrivial ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj L.sheaf) := nontrivial_of_ne z 0 hz
  exact Module.finrank_pos

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.LineBundleSectionDimension
