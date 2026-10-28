import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleSectionIdentity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Nonvanishing
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.LinearAlgebra.Dimension.Finite

/-! # Point Section Generation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.PointSectionGeneration

noncomputable section

/-! Positive section dimension produces an actual nonzero section.
On a Jacobson scheme, section generation can be checked at closed points. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem lineBundle_exists_nonzero_section_of_finrank_pos
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (L : Line.Bundles.LineBundle X)
    (h : 0 < Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj L.sheaf)) :
    ∃ s : Line.Bundles.structureModule X ⟶ L.sheaf, s ≠ 0 := by
  let W := (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj L.sheaf
  have : Nontrivial W := Module.nontrivial_of_finrank_pos h
  obtain ⟨z, hz⟩ := exists_ne (0 : W)
  let e := Global.ModuleSectionIdentity.coefficientGlobalSectionsNativeIso (Coefficient.ModulePresheaf.schemeCoefficientMap p) L.sheaf
  let s := (Global.Sections.moduleSectionHomEquiv L.sheaf).symm (e z)
  refine ⟨s, fun hs => ?_⟩
  have he : e z = 0 := by
    exact ((Global.Sections.moduleSectionHomEquiv L.sheaf).apply_symm_apply (e z)).symm.trans
      ((congrArg (Global.Sections.moduleSectionHomEquiv L.sheaf) hs).trans (by rfl))
  exact hz (e.injective (he.trans (map_zero e).symm))

theorem lineBundle_pointwise_sections_of_closedPoints
    {X : Scheme.{u}} [JacobsonSpace X] (L : Line.Bundles.LineBundle X)
    (h : ∀ x : X, IsClosed {x} →
      ∃ s : Line.Bundles.structureModule X ⟶ L.sheaf, x ∈ Ample.LineBundles.sectionNonvanishing s) :
    ∀ x : X, ∃ s : Line.Bundles.structureModule X ⟶ L.sheaf, x ∈ Ample.LineBundles.sectionNonvanishing s := by
  let V : X.Opens := ⨆ s : Line.Bundles.structureModule X ⟶ L.sheaf, Ample.LineBundles.sectionNonvanishing s
  have hall : V = ⊤ := by
    apply top_unique
    intro x _
    by_contra hx
    obtain ⟨y, hy, hcy⟩ := nonempty_inter_closedPoints
      (show ((V : Set X)ᶜ).Nonempty from ⟨x, hx⟩) V.isOpen.isClosed_compl.isLocallyClosed
    obtain ⟨s, hs⟩ := h y hcy
    exact hy (show y ∈ V from (le_iSup (fun t => Ample.LineBundles.sectionNonvanishing t) s) hs)
  intro x
  have hx : x ∈ V := hall.symm ▸ (show x ∈ (⊤ : X.Opens) from trivial)
  simpa only [V, TopologicalSpace.Opens.mem_iSup] using hx

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.PointSectionGeneration
