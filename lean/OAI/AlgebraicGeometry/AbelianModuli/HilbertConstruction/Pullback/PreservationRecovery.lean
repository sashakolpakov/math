import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.IsomorphismDualDetermination
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.CompatibilityBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.PreservationProperties

/-! # Preservation Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! An actual moduli isomorphism whose abelian component is a prescribed pullback satisfies the corresponding pulled-back polarization and full-level equations. Poincare compatibility recovers its dual component. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

theorem Moduli.Isomorphisms.LevelPreservingIso.pullback_preservation_conditions
    {S T : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (f : A.abelian.scheme ⟶ B.abelian.scheme) (d : A.dual.abelian.scheme ⟶ B.dual.abelian.scheme)
    (hD : Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ f).left (Line.Bundles.LineBundle.classOf B.dual.poincare) = Line.Bundles.LineBundle.classOf A.dual.poincare)
    (b : T ⟶ S) (e : Moduli.Isomorphisms.LevelPreservingIso (A.pullback b) (B.pullback b))
    (he : e.abelian.hom = (Over.pullback b).map f) :
    (Over.pullback b).map (A.polarization.isogeny.hom ≫ d) =
      (Over.pullback b).map (f ≫ B.polarization.isogeny.hom) ∧ Level.PreservationProperties.FullLevelPreservesPullback A.level B.level f b := by
  have hP := Poincare.CompatibilityBaseChange.poincareCompatibility_pullback A.dual B.dual d f hD b
  have hd : e.dual.hom = (Over.pullback b).map d :=
    e.dual_hom_eq_of_poincare ((Over.pullback b).map d)
      ((congrArg (fun a => Line.Bundles.LineBundle.pullbackClass ((Over.pullback b).map d ⊗ₘ a).left
        (Line.Bundles.LineBundle.classOf (B.dual.pullback b).poincare)) he).trans hP)
  constructor
  · have hp : (Over.pullback b).map A.polarization.isogeny.hom ≫ e.dual.hom =
        e.abelian.hom ≫ (Over.pullback b).map B.polarization.isogeny.hom := e.polarization
    exact ((Over.pullback b).map_comp A.polarization.isogeny.hom d).trans
      ((congrArg (fun z => (Over.pullback b).map A.polarization.isogeny.hom ≫ z) hd.symm).trans
        (hp.trans ((congrArg (fun z => z ≫ (Over.pullback b).map B.polarization.isogeny.hom) he).trans
          ((Over.pullback b).map_comp f B.polarization.isogeny.hom).symm)))
  · intro U z
    exact (congrArg (fun a => ((A.level.pullback b).hom.app (.op U) z).val ≫ a) he).symm.trans (e.level U z)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
