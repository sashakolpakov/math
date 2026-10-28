import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.PullHom
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentReindexing

/-! # Fibers -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

noncomputable section

/-!
# Actual line-bundle fibers and their bilinear operations on arbitrary test schemes
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{u}} {A : Over S} (L : Bundles.LineBundle A.left)

/-- The actual module sheaf obtained by pulling the line bundle to a test point. -/
def fiber {T : Over S} (x : T ⟶ A) : T.left.Modules := (Scheme.Modules.pullback x.left).obj L.sheaf

/-- Every test-scheme fiber is still an actual line bundle. -/
theorem fiber_isLine {T : Over S} (x : T ⟶ A) : Bundles.IsLine (fiber L x) :=
  L.isLine.pullback x.left

/-- The standard pullback composition identifies the fibers after change of test scheme. -/
def fiberPullbackIso {T T' : Over S} (g : T' ⟶ T) (x : T ⟶ A) (x' : T' ⟶ A) (hx : g ≫ x = x') :
    (Scheme.Modules.pullback g.left).obj (fiber L x) ≅ fiber L x' :=
  (Scheme.Modules.pullbackComp g.left x.left ≪≫
    Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hx)).app L.sheaf

/-- Native pseudofunctor transport uses precisely these actual fiber pullback isomorphisms. -/
theorem pullHom_eq {T T' : Over S} {x y : T ⟶ A} (a : fiber L x ⟶ fiber L y)
    (g : T' ⟶ T) (x' y' : T' ⟶ A) (hx : g ≫ x = x') (hy : g ≫ y = y') :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := Geometric.KernelLinearization.overModulePullbacks S) a g x' y' hx hy =
      (fiberPullbackIso L g x x' hx).inv ≫ (Scheme.Modules.pullback g.left).map a ≫
        (fiberPullbackIso L g y y' hy).hom := by
  have hr := DescentReindexing.pullHom_reindex (Over.forget S) Geometric.KernelLinearization.modulePullbacks a g x' y' hx hy
  exact hr.trans (Geometric.PullHom.pullHom_eq a g.left x'.left y'.left
    (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy))

/-- Pull back a normalized section of a test-point fiber through its actual fiber comparison. -/
def pullSection {T T' : Over S} (g : T' ⟶ T) (x : T ⟶ A) (x' : T' ⟶ A) (hx : g ≫ x = x')
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ⟶ fiber L x) : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T'.left ⟶ fiber L x' :=
  Bilinear.ContractionPullback.pulledSection g.left s ≫ (fiberPullbackIso L g x x' hx).hom

/-- Pull back a bilinear operation on actual fibers to specified points on the new test scheme. -/
def pullBilinear {T T' : Over S} (g : T' ⟶ T) (x y z : T ⟶ A)
    (x' y' z' : T' ⟶ A) (hx : g ≫ x = x') (hy : g ≫ y = y') (hz : g ≫ z = z')
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (fiber L x) (fiber L y) (fiber L z)) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (fiber L x') (fiber L y') (fiber L z') :=
  Bilinear.Transport.transport
    (Bilinear.BilinearPullback.pullback g.left (fiber_isLine L x) (fiber_isLine L y) β)
    (fiberPullbackIso L g x x' hx) (fiberPullbackIso L g y y' hy) (fiberPullbackIso L g z z' hz)

/-- Insertion of a normalized fiber section has exactly the native geometric descent naturality. -/
theorem contraction_pullback {T T' : Over S} (g : T' ⟶ T) (x y z : T ⟶ A)
    (x' y' z' : T' ⟶ A) (hx : g ≫ x = x') (hy : g ≫ y = y') (hz : g ≫ z = z')
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (fiber L x) (fiber L y) (fiber L z)) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ⟶ fiber L x) :
    Bilinear.Contraction.contractLeft (pullBilinear L g x y z x' y' z' hx hy hz β)
      (pullSection L g x x' hx s) =
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := Geometric.KernelLinearization.overModulePullbacks S)
      (Bilinear.Contraction.contractLeft β s) g y' z' hy hz := by
  exact (Bilinear.Transport.contractLeft_pullback_transport g.left (fiber_isLine L x) (fiber_isLine L y) β
    (fiberPullbackIso L g x x' hx) (fiberPullbackIso L g y y' hy) (fiberPullbackIso L g z z' hz) s).trans
      (pullHom_eq L (Bilinear.Contraction.contractLeft β s) g y' z' hy hz).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers
