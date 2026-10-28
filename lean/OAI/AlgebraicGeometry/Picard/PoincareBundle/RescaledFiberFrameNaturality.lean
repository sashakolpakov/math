import OAI.AlgebraicGeometry.Picard.PoincareBundle.RescaledLineFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberFrameRatios

/-! # Rescaled Fiber Frame Naturality -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.RescaledFiberFrameNaturality

noncomputable section

/-! Regular rescalings of line-fiber frames respect the canonical pullback comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.RescaledLineFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar

variable {X : Scheme.{u}} {M N : X.Modules}

/-- Scalar correction commutes with an actual line-sheaf isomorphism. -/
theorem rescale_postcomp (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ≅ M) (r : Γ(X, ⊤)ˣ) (e : M ≅ N) :
    RescaledLineFrames.rescale s r ≪≫ e = RescaledLineFrames.rescale (s ≪≫ e) r := by
  apply Iso.ext
  change (s.hom ≫ Isogenies.NeighborCounting.ModuleScalar.scalarEnd M (r : Γ(X, ⊤))) ≫ e.hom =
    (s.hom ≫ e.hom) ≫ Isogenies.NeighborCounting.ModuleScalar.scalarEnd N (r : Γ(X, ⊤))
  rw [Category.assoc, Isogenies.NeighborCounting.ModuleScalar.scalarEnd_naturality, Category.assoc]

variable {S : Scheme.{u}} {H : Over S} (L : Line.Bundles.LineBundle H.left)
  {T U : Over S} (g : U ⟶ T) (a : T ⟶ H) (a' : U ⟶ H) (ha : g ≫ a = a')
  (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L a) (s' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.left ≅ Line.Fibers.fiber L a')
  (r : Γ(T.left, ⊤)ˣ) (r' : Γ(U.left, ⊤)ˣ)

/-- Naturality of both the frame and its regular unit implies naturality of the corrected frame. -/
theorem rescale_natural
    (hs : Line.Fibers.pullSection L g a a' ha s.hom = s'.hom)
    (hr : Units.map g.left.appTop.hom r = r') :
    Line.Fibers.pullSection L g a a' ha (RescaledLineFrames.rescale s r).hom = (RescaledLineFrames.rescale s' r').hom := by
  have hp := FiberFrameRatios.pullFrame_eq L g a a' ha s s' hs
  have h : FrameRatioPullback.pullFrame g.left (RescaledLineFrames.rescale s r) ≪≫ Line.Fibers.fiberPullbackIso L g a a' ha = RescaledLineFrames.rescale s' r' := by
    rw [RescaledLineFrames.rescale_pullback, rescale_postcomp, hp, hr]
  exact congrArg Iso.hom h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.RescaledFiberFrameNaturality
