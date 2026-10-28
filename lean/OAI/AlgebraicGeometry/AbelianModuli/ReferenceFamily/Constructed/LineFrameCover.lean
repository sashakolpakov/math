import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalSheaf
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Frames

/-! # Line Frame Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.LineFrameCover

noncomputable section

/-! Every original line bundle has an actual affine frame cover.
Its native local frames supply their compatible regular-function
transition cocycle on the original covering opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X : Scheme.{0}} {I : Type} {M : X.Modules}

def localLineFrameNaturalFrames (s : I → LineFrameAtlas.LocalLineFrame M) :
    HilbertConstruction.NaturalSheaf.NaturalSheafFrames (fun i => (s i).domain) M where
  frame V i hi := ((s i).coordinates V hi).symm
  restrict V W h i hi r := by
    apply ((s i).coordinates W (h.trans hi)).injective
    rw [(s i).coordinates_restrict h hi, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem localLineFrameNaturalFrames_transition (s : I → LineFrameAtlas.LocalLineFrame M) (V : X.Opens)
    (i j : I) (hi : V ≤ (s i).domain) (hj : V ≤ (s j).domain) :
    (localLineFrameNaturalFrames s).transitions.value V i j hi hj =
      (s i).transition (s j) V hi hj := by
  apply Units.ext
  rfl

structure LineBundleAffineFrameCover (L : HilbertConstruction.Line.Bundles.LineBundle X) where
  cover : X.AffineOpenCover
  frame : ∀ i : cover.I₀,
    L.sheaf.restrict (cover.f i).opensRange.ι ≅ HilbertConstruction.Line.Bundles.structureModule (cover.f i).opensRange.toScheme

def lineBundleAffineFrameCover (L : HilbertConstruction.Line.Bundles.LineBundle X) : LineBundleAffineFrameCover L := by
  classical
  choose V hx ha he using L.exists_affine_frame
  have hV : IsOpenCover V := by
    rw [IsOpenCover]
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  let U := Scheme.AffineOpenCover.ofIsOpenCover V hV ha
  refine ⟨U, fun i => ?_⟩
  have hi : (U.f i).opensRange = V i := (ha i).opensRange_fromSpec
  let e : L.sheaf.restrict (V i).ι ≅ HilbertConstruction.Line.Bundles.structureModule (V i).toScheme :=
    (Scheme.Modules.restrictFunctorIsoPullback (V i).ι).app L.sheaf ≪≫ (he i).some
  exact hi.symm ▸ e

namespace LineBundleAffineFrameCover

variable {L : HilbertConstruction.Line.Bundles.LineBundle X} (C : LineBundleAffineFrameCover L)

def localFrame (i : C.cover.I₀) : LineFrameAtlas.LocalLineFrame L.sheaf := ⟨(C.cover.f i).opensRange, C.frame i⟩

def transitions : HilbertConstruction.OpenFrame.Transitions.OpenFrameTransitions (fun i => (C.cover.f i).opensRange) :=
  (localLineFrameNaturalFrames C.localFrame).transitions

def compatibleFrames : HilbertConstruction.CompatibleSheaf.CompatibleSheafFrames C.transitions L.sheaf :=
  (localLineFrameNaturalFrames C.localFrame).compatible

theorem transition_eq_original (V : X.Opens) (i j : C.cover.I₀)
    (hi : V ≤ (C.cover.f i).opensRange) (hj : V ≤ (C.cover.f j).opensRange) :
    C.transitions.value V i j hi hj = (C.localFrame i).transition (C.localFrame j) V hi hj :=
  localLineFrameNaturalFrames_transition C.localFrame V i j hi hj

end LineBundleAffineFrameCover

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.LineFrameCover
