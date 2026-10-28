import Mathlib.AlgebraicGeometry.Cover.Directed

/-! # Open Refinement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.OpenRefinement

noncomputable section

/-! Every open cover admits a locally directed refinement by affine open subschemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

/-- Refine every member of a cover by all of its affine open subschemes. -/
def directedOpenRefinement (C : X.OpenCover) : X.OpenCover :=
  C.bind (fun i => (C.X i).directedAffineCover)

/-- Order the refined cover by inclusion of the images in the original scheme. -/
instance directedOpenRefinement_preorder (C : X.OpenCover) :
    Preorder (directedOpenRefinement C).I₀ :=
  Preorder.lift (fun i => ((directedOpenRefinement C).f i).opensRange)

/-- The refined affine images form a basis of the ambient topology. -/
theorem directedOpenRefinement_isBasis (C : X.OpenCover) :
    TopologicalSpace.Opens.IsBasis
      (Set.range (fun i => ((directedOpenRefinement C).f i).opensRange)) := by
  apply TopologicalSpace.Opens.isBasis_iff_nbhd.mpr
  intro U x hx
  obtain ⟨i, y, rfl⟩ := C.exists_eq x
  obtain ⟨V, hV, hy, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (C.X i).isBasis_affineOpens (show y ∈ (C.f i) ⁻¹ᵁ U from hx)
  let k : (directedOpenRefinement C).I₀ := ⟨i, ⟨V, hV⟩⟩
  refine ⟨((directedOpenRefinement C).f k).opensRange, ⟨k, rfl⟩, ?_, ?_⟩
  · exact ⟨⟨y, hy⟩, rfl⟩
  · rintro z ⟨w, rfl⟩
    exact hVU w.property

/-- Every ordinary open cover thus has a locally directed affine refinement. -/
instance directedOpenRefinement_locallyDirected (C : X.OpenCover) :
    (directedOpenRefinement C).LocallyDirected :=
  Scheme.Cover.LocallyDirected.ofIsBasisOpensRange Iff.rfl (directedOpenRefinement_isBasis C)

/-- Each refined member has its original inclusion into a member of the given cover. -/
def directedOpenRefinement_toMember (C : X.OpenCover) (i : (directedOpenRefinement C).I₀) :
    (directedOpenRefinement C).X i ⟶ C.X i.1 :=
  (C.X i.1).directedAffineCover.f i.2

theorem directedOpenRefinement_toMember_map (C : X.OpenCover) (i : (directedOpenRefinement C).I₀) :
    directedOpenRefinement_toMember C i ≫ C.f i.1 = (directedOpenRefinement C).f i := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Directed.OpenRefinement
