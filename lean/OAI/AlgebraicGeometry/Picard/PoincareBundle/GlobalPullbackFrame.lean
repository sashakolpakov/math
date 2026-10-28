import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FramePullbackComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

/-! # Global Pullback Frame -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

noncomputable section

/-!
# A genuine global pullback trivialization gives canonical frames on all test fibers
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{u}} {K E : Over S} (p : K ⟶ E) (L : Line.Bundles.LineBundle E.left)

/-- The actual composition comparison identifies the fiber over a lifted point with the original line fiber. -/
def comparison {T : Over S} (k : T ⟶ K) (x : T ⟶ E) (hk : k ≫ p = x) :
    (Scheme.Modules.pullback k.left).obj ((Scheme.Modules.pullback p.left).obj L.sheaf) ≅ Line.Fibers.fiber L x :=
  PullbackFiberComposition.fiberIsoTo (Geometric.KernelLinearization.overModulePullbacks S) p L.sheaf k x hk

/-- The native comparison is exactly the canonical composition and equality isomorphism of module sheaves. -/
theorem comparison_eq {T : Over S} (k : T ⟶ K) (x : T ⟶ E) (hk : k ≫ p = x) :
    comparison p L k x hk =
      (Scheme.Modules.pullbackComp k.left p.left ≪≫
        Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hk)).app L.sheaf := by
  subst x
  apply Iso.ext
  rfl

variable (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule K.left ≅ (Scheme.Modules.pullback p.left).obj L.sheaf)

/-- Pull the actual global trivialization to a lifted point and identify its target fiber canonically. -/
def atPoint {T : Over S} (k : T ⟶ K) (x : T ⟶ E) (hk : k ≫ p = x) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L x := FrameRatioPullback.pullFrame k.left s ≪≫ comparison p L k x hk

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame
