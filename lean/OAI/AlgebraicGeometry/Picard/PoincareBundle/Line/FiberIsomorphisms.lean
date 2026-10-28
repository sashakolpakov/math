import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.TransportComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.FrameProducts
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

/-! # Fiber Isomorphisms -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FiberIsomorphisms

noncomputable section

/-!
# Actual line-bundle isomorphisms transport all fiber sections and operations geometrically
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ContractionPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.TransportComposition

variable {S : Scheme.{u}} {E : Over S} (L M : Bundles.LineBundle E.left) (e : L.sheaf ≅ M.sheaf)

/-- An actual line-bundle isomorphism induces an isomorphism at every test-scheme fiber. -/
def fiberIso {T : Over S} (x : T ⟶ E) : Fibers.fiber L x ≅ Fibers.fiber M x := (Scheme.Modules.pullback x.left).mapIso e

/-- The entire actual fiber-isomorphism square commutes with change of test scheme. -/
theorem fiberIso_pullback {T T' : Over S} (g : T' ⟶ T) (x : T ⟶ E) (x' : T' ⟶ E) (hx : g ≫ x = x') :
    (Scheme.Modules.pullback g.left).mapIso (fiberIso L M e x) ≪≫ Fibers.fiberPullbackIso M g x x' hx =
      Fibers.fiberPullbackIso L g x x' hx ≪≫ fiberIso L M e x' := by
  apply Iso.ext
  exact (Scheme.Modules.pullbackComp g.left x.left ≪≫
    Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hx)).hom.naturality e.hom

/-- A normalized section is transported by the actual pulled-back line-bundle isomorphism. -/
def transportSection {T : Over S} (x : T ⟶ E) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ⟶ Fibers.fiber L x) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ⟶ Fibers.fiber M x := s ≫ (fiberIso L M e x).hom

/-- Actual line-bundle isomorphisms preserve geometric naturality of normalized sections. -/
theorem transportSection_pullback {T T' : Over S} (g : T' ⟶ T) (x : T ⟶ E) (x' : T' ⟶ E)
    (hx : g ≫ x = x') (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ⟶ Fibers.fiber L x) :
    Fibers.pullSection M g x x' hx (transportSection L M e x s) =
      transportSection L M e x' (Fibers.pullSection L g x x' hx s) := by
  have he := congrArg Iso.hom (fiberIso_pullback L M e g x x' hx)
  unfold transportSection Fibers.pullSection
  rw [Bilinear.FrameProducts.pulledSection_comp]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => Bilinear.ContractionPullback.pulledSection g.left s ≫ f) he).trans (Category.assoc _ _ _).symm)

/-- Transport an actual normalized frame of a test fiber. -/
def transportFrame {T : Over S} (x : T ⟶ E) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Fibers.fiber L x) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Fibers.fiber M x := s ≪≫ fiberIso L M e x

/-- The actual transported normalized frame satisfies the original geometric naturality equation. -/
theorem transportFrame_natural {T T' : Over S} (g : T' ⟶ T) (x : T ⟶ E) (x' : T' ⟶ E)
    (hx : g ≫ x = x') (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Fibers.fiber L x)
    (s' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T'.left ≅ Fibers.fiber L x') (hs : Fibers.pullSection L g x x' hx s.hom = s'.hom) :
    Fibers.pullSection M g x x' hx (transportFrame L M e x s).hom = (transportFrame L M e x' s').hom := by
  have he := transportSection_pullback L M e g x x' hx s.hom
  rw [hs] at he
  exact he

/-- Transport a genuine fiber-bilinear operation by the actual line-bundle isomorphism. -/
def transportBilinear {T : Over S} (x y z : T ⟶ E)
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Fibers.fiber L x) (Fibers.fiber L y) (Fibers.fiber L z)) :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Fibers.fiber M x) (Fibers.fiber M y) (Fibers.fiber M z) :=
  Bilinear.Transport.transport β (fiberIso L M e x) (fiberIso L M e y) (fiberIso L M e z)

/-- The actual transported bilinear operation retains its full geometric pullback law. -/
theorem transportBilinear_pullback {T T' : Over S} (g : T' ⟶ T)
    (x y z : T ⟶ E) (x' y' z' : T' ⟶ E) (hx : g ≫ x = x') (hy : g ≫ y = y') (hz : g ≫ z = z')
    (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Fibers.fiber L x) (Fibers.fiber L y) (Fibers.fiber L z)) :
    Fibers.pullBilinear M g x y z x' y' z' hx hy hz (transportBilinear L M e x y z β) =
      transportBilinear L M e x' y' z' (Fibers.pullBilinear L g x y z x' y' z' hx hy hz β) := by
  unfold transportBilinear Fibers.pullBilinear
  rw [Bilinear.TransportComposition.pullback_transport g.left (Fibers.fiber_isLine L x) (Fibers.fiber_isLine L y) (Fibers.fiber_isLine M x) (Fibers.fiber_isLine M y)
    β (fiberIso L M e x) (fiberIso L M e y) (fiberIso L M e z), Bilinear.TransportComposition.transport_trans,
    fiberIso_pullback L M e g x x' hx, fiberIso_pullback L M e g y y' hy,
    fiberIso_pullback L M e g z z' hz, ← Bilinear.TransportComposition.transport_trans]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FiberIsomorphisms
