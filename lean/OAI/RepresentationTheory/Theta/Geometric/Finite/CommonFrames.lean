import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Frames

/-! # Common Frames -/

namespace OAI.RepresentationTheory.Theta.Geometric.Finite.CommonFrames

noncomputable section

/-! Two actual line bundles on a quasi-compact scheme admit one finite
affine cover with native frames for both bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_common_affine_frame {X : Scheme} (L N : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L.sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj N.sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.toScheme) := by
  obtain ⟨V, hxV, ⟨eL⟩⟩ := L.locallyTrivial x
  obtain ⟨W, hxW, ⟨eN⟩⟩ := N.locallyTrivial x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ V ⊓ W from ⟨hxV, hxW⟩) (V ⊓ W).isOpen
  exact ⟨U, hxU, hU, ⟨L.frameRestrict (hUV.trans inf_le_left) eL⟩,
    ⟨N.frameRestrict (hUV.trans inf_le_right) eN⟩⟩

theorem exists_finite_common_affine_frames {X : Scheme} [CompactSpace X]
    (L N : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    ∃ (k : ℕ) (U : Fin k → X.Opens), (∀ i, IsAffineOpen (U i)) ∧
      (∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (U i).toScheme)) ∧
      (∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj N.sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (U i).toScheme)) ∧
      iSup U = ⊤ := by
  classical
  choose U hx hU eL eN using exists_common_affine_frame L N
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (U x : Set X)) (fun x => (U x).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let a := Fintype.equivFin t
  refine ⟨Fintype.card t, fun i => U (a.symm i).val, fun i => hU _, fun i => eL _, fun i => eN _, ?_⟩
  apply top_unique
  intro x _
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨a ⟨y, hy⟩, ?_⟩
  have he : (a.symm (a ⟨y, hy⟩)).val = y := congrArg Subtype.val (a.symm_apply_apply ⟨y, hy⟩)
  exact (congrArg (fun z => x ∈ U z) he).mpr hxy

end

end OAI.RepresentationTheory.Theta.Geometric.Finite.CommonFrames
