import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Quasicoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineBundles

/-! # Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Affine local frames, finite frame covers, and quasi-coherence under restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (L : Line.Bundles.LineBundle X)

/-- Quasi-coherence of a line bundle also applies to the concrete restriction
functor on open subschemes. -/
theorem Line.Bundles.LineBundle.restrict_isQuasicoherent (f : Y ⟶ X) [IsOpenImmersion f] :
    (L.sheaf.restrict f).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback f).app L.sheaf).symm
    (L.pullback f).isQuasicoherent

/-- Every point has an affine neighborhood on which the line bundle is trivial. -/
theorem Line.Bundles.LineBundle.exists_affine_frame (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L.sheaf ≅ Line.Bundles.structureModule U.toScheme) := by
  obtain ⟨V, hxV, ⟨e⟩⟩ := L.locallyTrivial x
  obtain ⟨_, ⟨U : X.Opens, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  exact ⟨U, hxU, hU, ⟨L.frameRestrict hUV e⟩⟩

/-- On a quasi-compact scheme, finitely many affine frames suffice. -/
theorem Line.Bundles.LineBundle.exists_finite_affine_frames [CompactSpace X] :
    ∃ (k : ℕ) (U : Fin k → X.Opens),
      (∀ i, IsAffineOpen (U i)) ∧
      (∀ i, Nonempty ((Scheme.Modules.pullback (U i).ι).obj L.sheaf ≅
        Line.Bundles.structureModule (U i).toScheme)) ∧
      ∀ x : X, ∃ i, x ∈ U i := by
  classical
  choose U hx hU e using L.exists_affine_frame
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (U x : Set X)) (fun x => (U x).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let a := Fintype.equivFin t
  refine ⟨Fintype.card t, fun i => U (a.symm i).val, fun i => hU _, fun i => e _, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  refine ⟨a ⟨y, hy⟩, ?_⟩
  have he : (a.symm (a ⟨y, hy⟩)).val = y := congrArg Subtype.val (a.symm_apply_apply ⟨y, hy⟩)
  exact (congrArg (fun z => x ∈ U z) he).mpr hxy

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
