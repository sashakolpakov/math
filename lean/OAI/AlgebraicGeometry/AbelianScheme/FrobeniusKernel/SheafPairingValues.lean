import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafBlocks

/-! # Sheaf Pairing Values -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SheafPairingValues.Construction

/-! Restriction preserves the literal all-test values of a sheaf pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem sheafPairing_restrict_value {S : Scheme} {G H G' H' : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (e : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing G H) (i : G' ⟶ G) (j : H' ⟶ H)
    (T : Over S) (x : G'.obj.obj (.op T)) (y : H'.obj.obj (.op T)) :
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue G' T ((e.restrict i j).rightAdjoint.hom.app (.op T) y) x =
      CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue G T (e.rightAdjoint.hom.app (.op T) (j.hom.app (.op T) y))
        (i.hom.app (.op T) x) :=
  (congrArg (fun f => CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue G' T (f.hom.app (.op T) y) x)
    (CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.restrict_rightAdjoint e i j)).trans
      (CartierDuality.SheafEvaluation.Construction.Schemes.cartierDualSheafMap_value i T (e.rightAdjoint.hom.app (.op T) (j.hom.app (.op T) y)) x)

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SheafPairingValues.Construction
