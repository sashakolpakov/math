import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ActionLaws

/-! # Square -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Square

noncomputable section

/-!
# The isotropy calculation for the two translations of a biextension

The six maps below are the horizontal and vertical products in an actual square of line fibers.
The interchange law and equality of the two frames at the kernel intersection prove that the
induced translations commute. No commuting-action or descent conclusion is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction

variable {X : Scheme.{u}} {C K L M P Q K' L' R : X.Modules}

/-- Multiplicative frames which agree at the crossing give a commuting square of actual sheaf maps. -/
theorem translations_commute
    (horizontal : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap K M P) (vertical : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap L M Q)
    (horizontalCross : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap C L L') (verticalCross : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap C K K')
    (verticalEnd : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap L' P R) (horizontalEnd : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap K' Q R)
    (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ K) (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L)
    (s' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ K') (t' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L')
    (crossHorizontal crossVertical : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ C)
    (interchange : ∀ (U : X.Opens) (c : Γ(C, U)) (k : Γ(K, U)) (l : Γ(L, U)) (m : Γ(M, U)),
      verticalEnd.app U (horizontalCross.app U c l) (horizontal.app U k m) =
        horizontalEnd.app U (verticalCross.app U c k) (vertical.app U l m))
    (horizontalFrame : ∀ U : X.Opens,
      horizontalCross.app U (crossVertical.app U (1 : Γ(X, U))) (t.app U (1 : Γ(X, U))) =
        t'.app U (1 : Γ(X, U)))
    (verticalFrame : ∀ U : X.Opens,
      verticalCross.app U (crossHorizontal.app U (1 : Γ(X, U))) (s.app U (1 : Γ(X, U))) =
        s'.app U (1 : Γ(X, U)))
    (isotropic : crossHorizontal = crossVertical) :
    Bilinear.Contraction.contractLeft horizontal s ≫ Bilinear.Contraction.contractLeft verticalEnd t' =
      Bilinear.Contraction.contractLeft vertical t ≫ Bilinear.Contraction.contractLeft horizontalEnd s' := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  change (Bilinear.Contraction.contractLeft verticalEnd t').app U ((Bilinear.Contraction.contractLeft horizontal s).app U m) =
    (Bilinear.Contraction.contractLeft horizontalEnd s').app U ((Bilinear.Contraction.contractLeft vertical t).app U m)
  rw [Bilinear.Contraction.contractLeft_app, Bilinear.Contraction.contractLeft_app, Bilinear.Contraction.contractLeft_app, Bilinear.Contraction.contractLeft_app,
    ← horizontalFrame, ← verticalFrame, isotropic]
  exact interchange U _ _ _ m

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Square
