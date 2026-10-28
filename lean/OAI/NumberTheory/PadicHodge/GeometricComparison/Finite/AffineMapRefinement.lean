import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.AffineRefinement

/-! # Affine Map Refinement -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.AffineMapRefinement.FiniteAffineMapRefinement

noncomputable section

/-! A quasi-compact source has an actual finite affine cover refining both a chosen source cover and the inverse image of a chosen target cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X Y : Scheme.{0}} (f : X ⟶ Y) {ι κ : Type}
  (U : ι → Y.Opens) (V : κ → X.Opens)

def intersections : ι × κ → X.Opens := fun i => V i.2 ⊓ f ⁻¹ᵁ U i.1

theorem cover (hU : iSup U = ⊤) (hV : iSup V = ⊤) : iSup (intersections f U V) = ⊤ := by
  apply top_le_iff.mp
  intro x _
  have hy : f x ∈ iSup U := hU.symm ▸ (show f x ∈ (⊤ : Y.Opens) from trivial)
  have hx : x ∈ iSup V := hV.symm ▸ (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
  exact Opens.mem_iSup.mpr ⟨(i, j), hj, hi⟩

def ofCompact [CompactSpace X] (hU : iSup U = ⊤) (hV : iSup V = ⊤) :
    AffineRefinement.FiniteAffineRefinement.Refinement (intersections f U V) :=
  AffineRefinement.FiniteAffineRefinement.ofCompact (intersections f U V) (cover f U V hU hV)

theorem le_source [CompactSpace X] (hU : iSup U = ⊤) (hV : iSup V = ⊤)
    (i : (ofCompact f U V hU hV).Index) :
    (ofCompact f U V hU hV).opens i ≤ f ⁻¹ᵁ U ((ofCompact f U V hU hV).index i).1 :=
  ((ofCompact f U V hU hV).le i).trans inf_le_right

theorem le_target [CompactSpace X] (hU : iSup U = ⊤) (hV : iSup V = ⊤)
    (i : (ofCompact f U V hU hV).Index) :
    (ofCompact f U V hU hV).opens i ≤ V ((ofCompact f U V hU hV).index i).2 :=
  ((ofCompact f U V hU hV).le i).trans inf_le_left

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.AffineMapRefinement.FiniteAffineMapRefinement
