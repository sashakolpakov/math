import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.CompatibilityBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PreservationProperties

/-! # Pulled Back Isomorphism Constructor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual compatible abelian and dual isomorphisms give a moduli isomorphism on any base change where the polarization and full-level equations hold. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.Obj

universe u

def Moduli.Isomorphisms.LevelPreservingIso.ofPullbackMaps {S T : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (e : A.abelian.scheme ≅ B.abelian.scheme) (d : A.dual.abelian.scheme ≅ B.dual.abelian.scheme)
    [IsMonHom e.hom] [IsMonHom d.hom]
    (hD : Line.Bundles.LineBundle.pullbackClass (d.hom ⊗ₘ e.hom).left
      (Line.Bundles.LineBundle.classOf B.dual.poincare) = Line.Bundles.LineBundle.classOf A.dual.poincare)
    (b : T ⟶ S)
    (hp : (Over.pullback b).map (A.polarization.isogeny.hom ≫ d.hom) =
      (Over.pullback b).map (e.hom ≫ B.polarization.isogeny.hom))
    (hl : Level.PreservationProperties.FullLevelPreservesPullback A.level B.level e.hom b) :
    Moduli.Isomorphisms.LevelPreservingIso (A.pullback b) (B.pullback b) where
  abelian := (Over.pullback b).mapIso e
  dual := (Over.pullback b).mapIso d
  abelianGroup := inferInstanceAs (IsMonHom ((Over.pullback b).map e.hom))
  dualGroup := inferInstanceAs (IsMonHom ((Over.pullback b).map d.hom))
  polarization := ((Over.pullback b).map_comp A.polarization.isogeny.hom d.hom).symm.trans
    (hp.trans ((Over.pullback b).map_comp e.hom B.polarization.isogeny.hom))
  poincare := Poincare.CompatibilityBaseChange.poincareCompatibility_pullback A.dual B.dual d.hom e.hom hD b
  level := hl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
