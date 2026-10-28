import OAI.AlgebraicGeometry.Picard.PoincareBundle.FramedDescentIso
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineCharacterIndependence

/-! # Scalar Line Iso -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.ScalarLineIso

noncomputable section

/-! Actual line isomorphisms preserve canonical descent scalars in the transported frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {L M : Y.Modules} (e : L ≅ M)
  (s : (Scheme.Modules.pullback f).obj L ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)

/-- Transport the actual global pulled frame along the pulled line isomorphism. -/
def frame : (Scheme.Modules.pullback f).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X :=
  ((Scheme.Modules.pullback f).mapIso e).symm ≪≫ s

/-- Canonical gluing and its exact scalar commute with the line isomorphism. -/
theorem scalar_eq {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
    (hx : x ≫ f = q) (hy : y ≫ f = q) :
    Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f M) (frame f e s) q x y hx hy =
      Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f L) s q x y hx hy :=
  FramedDescentIso.scalar_eq (Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f L) (Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f M)
    ((Scheme.Modules.pullback f).mapIso e) s q x y hx hy
    (AbelianScheme.CartierDuality.LineCharacterIndependence.Construction.KernelCharacters.canonicalDescent_naturality f e.hom q x y hx hy)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.ScalarLineIso
