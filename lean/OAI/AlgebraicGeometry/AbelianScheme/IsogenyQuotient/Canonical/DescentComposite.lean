import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.DescentSquare
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineCharacterIndependence

/-! # Descent Composite -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.DescentComposite.Construction

noncomputable section

/-! When source functions come from the parameter base, a framed
scalar for a pulled-back line equals the scalar for its composite map.
The comparison is independent of the chosen pullback frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineCharacterIndependence.Construction.KernelCharacters

universe u

theorem canonicalDescentScalar_composite {S X Y Z T : Scheme.{u}}
    (p : X ⟶ S) (hp : Function.Surjective p.appTop)
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hw : f ≫ g = h)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Z)
    (e : (Scheme.Modules.pullback h).obj L.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (d : (Scheme.Modules.pullback f).obj (L.pullback g).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q)
    (hbase : x ≫ p = y ≫ p) :
    Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f (L.pullback g).sheaf) d q x y hx hy =
      Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent h L.sheaf) e (q ≫ g) x y
        (by rw [← hw, ← Category.assoc, hx]) (by rw [← hw, ← Category.assoc, hy]) := by
  let w : (𝟙 X) ≫ h = f ≫ g := (Category.id_comp h).trans hw.symm
  let r := DescentSquare.Construction.canonicalSquareFrame h f g (𝟙 X) w L.sheaf e
  have hr := CartierDuality.LineCharacterIndependence.Construction.KernelCharacters.canonicalScalar_eq_of_lineIso p hp f (L.pullback g) (L.pullback g) (Iso.refl _) d r
    q x y hx hy hbase
  have hs := DescentSquare.Construction.canonicalDescentScalar_square h f g (𝟙 X) w L.sheaf e q x y hx hy
  exact hr.trans (hs.trans (Picard.Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar_congr (Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent h L.sheaf) e
    _ _ _ _ _ _ _ _ _ _ rfl (Category.comp_id x) (Category.comp_id y)))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.DescentComposite.Construction
