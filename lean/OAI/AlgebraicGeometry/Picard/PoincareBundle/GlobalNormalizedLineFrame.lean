import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineData
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FramePullbackComposition
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.RigidifiedIso

/-! # Global Normalized Line Frame -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalNormalizedLineFrame

noncomputable section

/-! A global line frame can be normalized at the group identity by a regular scalar from the base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineData OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback

variable {S : Scheme.{u}} {H : Over S} [GrpObj H]
  (L : Line.Bundles.LineBundle H.left) (D : MultiplicativeLineData.MultiplicativeData L)
  (e : L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule H.left)

/-- The corrected global frame is constructed from the given identity trivialization. -/
def frame : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule H.left ≅ L.sheaf :=
  (Isogenies.NeighborCounting.RigidifiedIso.normalizedIso H.hom (1 : Over.mk (𝟙 S) ⟶ H).left e
    (D.unitFrame (T := Over.mk (𝟙 S))).symm
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (1 : Over.mk (𝟙 S) ⟶ H).left)).symm

/-- Its restriction to the identity is exactly the original multiplicative unit frame. -/
theorem frame_one :
    FrameRatioPullback.pullFrame (1 : Over.mk (𝟙 S) ⟶ H).left (frame L D e) = D.unitFrame := by
  have h := Isogenies.NeighborCounting.RigidifiedIso.normalizedIso_section H.hom
    (1 : Over.mk (𝟙 S) ⟶ H).left (1 : Over.mk (𝟙 S) ⟶ H).w e
    (D.unitFrame (T := Over.mk (𝟙 S))).symm
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (1 : Over.mk (𝟙 S) ⟶ H).left)
  have he : (Scheme.Modules.pullback (1 : Over.mk (𝟙 S) ⟶ H).left).mapIso (frame L D e).symm ≪≫
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (1 : Over.mk (𝟙 S) ⟶ H).left =
    (D.unitFrame (T := Over.mk (𝟙 S))).symm := Iso.ext h
  exact congrArg Iso.symm he

/-- Restrict the normalized global frame to any test-scheme point. -/
def atPoint {T : Over S} (a : T ⟶ H) : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L a :=
  FrameRatioPullback.pullFrame a.left (frame L D e)

/-- These frames respect the actual pullback comparisons of line fibers. -/
theorem atPoint_natural {T U : Over S} (g : U ⟶ T) (a : T ⟶ H) (a' : U ⟶ H) (ha : g ≫ a = a') :
    Line.Fibers.pullSection L g a a' ha (atPoint L D e a).hom = (atPoint L D e a').hom := by
  change (FrameRatioPullback.pullFrame g.left (atPoint L D e a) ≪≫ Line.Fibers.fiberPullbackIso L g a a' ha).hom =
    (atPoint L D e a').hom
  apply congrArg Iso.hom
  change FrameRatioPullback.pullFrame g.left (FrameRatioPullback.pullFrame a.left (frame L D e)) ≪≫
    ((Scheme.Modules.pullbackComp g.left a.left).app L.sheaf ≪≫
      (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left ha)).app L.sheaf) = _
  rw [← Iso.trans_assoc, FramePullbackComposition.pullFrame_comp]
  exact FramePullbackComposition.pullFrame_congr (g.left ≫ a.left) (frame L D e)
    a'.left (congrArg Over.Hom.left ha)

/-- Normalization persists at the identity over every test scheme. -/
theorem atPoint_one (T : Over S) : atPoint L D e (1 : T ⟶ H) = D.unitFrame := by
  let g : T ⟶ Over.mk (𝟙 S) := Over.homMk T.hom
  have hg : g ≫ (1 : Over.mk (𝟙 S) ⟶ H) = 1 := by simp
  have hn := atPoint_natural L D e g 1 1 hg
  have hzero : (atPoint L D e (1 : Over.mk (𝟙 S) ⟶ H)).hom = D.unitFrame.hom :=
    congrArg Iso.hom (frame_one L D e)
  apply Iso.ext
  exact hn.symm.trans ((congrArg (Line.Fibers.pullSection L g 1 1 hg) hzero).trans (D.unit_natural g hg))

/-- A global trivialization gives normalized natural fiber frames, with no supplied normalization law. -/
theorem exists_normalized_frames (he : Nonempty (L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule H.left)) :
    ∃ F : ∀ {T : Over S} (a : T ⟶ H), AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L a,
      (∀ T : Over S, F (1 : T ⟶ H) = D.unitFrame) ∧
      ∀ {T U : Over S} (g : U ⟶ T) (a : T ⟶ H) (a' : U ⟶ H) (ha : g ≫ a = a'),
        Line.Fibers.pullSection L g a a' ha (F a).hom = (F a').hom := by
  obtain ⟨s⟩ := he
  exact ⟨fun {T} a => atPoint L D s a, atPoint_one L D s, atPoint_natural L D s⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalNormalizedLineFrame
