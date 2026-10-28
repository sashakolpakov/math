import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Frames
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Frame Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-!
Finite affine spectrum covers carrying actual line-bundle frames. On a
separated scheme their pairwise fiber-product overlaps are affine as well.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X Y : Scheme.{u}}

/-- Morphisms from affine schemes to separated schemes are affine. -/
theorem Affine.FrameCover.affine_source_morphism_affine (f : Y ⟶ X) [IsAffine Y] [X.IsSeparated] :
    IsAffineHom f := by
  have : IsAffineHom (f ≫ terminal.from X) := inferInstance
  exact IsAffineHom.of_comp f (terminal.from X)

/-- Pairwise overlaps in an affine spectrum cover of a separated scheme are affine. -/
theorem Affine.FrameCover.affineCover_overlap_affine [X.IsSeparated] (C : X.AffineOpenCover)
    (i j : C.I₀) : IsAffine (pullback (C.f i) (C.f j)) := by
  have : IsAffineHom (C.f i) := Affine.FrameCover.affine_source_morphism_affine (C.f i)
  infer_instance

/-- A line bundle on a quasi-compact scheme has a finite affine spectrum cover
with an actual frame on every covering scheme. -/
theorem Line.Bundles.LineBundle.exists_finite_affine_frame_cover (L : Line.Bundles.LineBundle X) [CompactSpace X] :
    ∃ C : Scheme.AffineOpenCover.{0} X,
      Finite C.I₀ ∧ ∀ i, Nonempty ((Scheme.Modules.pullback (C.f i)).obj L.sheaf ≅
        Line.Bundles.structureModule (Spec (C.X i))) := by
  obtain ⟨k, U, ha, he, hcover⟩ := L.exists_finite_affine_frames
  have hU : IsOpenCover U := by
    rw [IsOpenCover]
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr (hcover x)
  let C := Scheme.AffineOpenCover.ofIsOpenCover U hU ha
  refine ⟨C, inferInstanceAs (Finite (Fin k)), fun i => ⟨?_⟩⟩
  exact (Scheme.Modules.pullbackComp (ha i).isoSpec.inv (U i).ι).symm.app L.sheaf ≪≫
    (Scheme.Modules.pullback (ha i).isoSpec.inv).mapIso (he i).some ≪≫
    Line.Bundles.structureModulePullbackIso (ha i).isoSpec.inv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
