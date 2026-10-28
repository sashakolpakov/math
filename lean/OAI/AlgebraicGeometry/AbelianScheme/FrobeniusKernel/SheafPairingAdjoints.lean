import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafBlocks
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Intertwining

/-! # Sheaf Pairing Adjoints -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SheafPairingAdjoints.Construction

/-! Character-valued squares give the adjoints of a pulled-back pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem projectorsAdjoint_of_rightMap {S : Scheme} {G H : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (e : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing G H) (p : G ⟶ G) (q : H ⟶ H)
    (h : q ≫ e.rightAdjoint = e.rightAdjoint ≫ (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map p.op) :
    CartierDuality.SheafBlocks.Construction.Schemes.ProjectorsAdjoint e p q := by
  intro T x y
  have ht := congrArg (fun f => f.hom.app (.op T) y) h
  exact (CartierDuality.SheafEvaluation.Construction.Schemes.cartierDualSheafMap_value p T (e.rightAdjoint.hom.app (.op T) y) x).symm.trans
    (congrArg (fun z => CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue G T z x) ht.symm)

theorem pairing_restrict_rightAdjoint {S : Scheme} {G H : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (e : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing G H) (ell : G ⟶ H) :
    (e.restrict (𝟙 G) ell).rightAdjoint = ell ≫ e.rightAdjoint := by
  have hi : (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map (𝟙 G).op = 𝟙 (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf G) :=
    (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).map_id (.op G)
  exact (CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.restrict_rightAdjoint e (𝟙 G) ell).trans
    ((congrArg (fun t => ell ≫ (e.rightAdjoint ≫ t)) hi).trans
      (congrArg (fun t => ell ≫ t) (Category.comp_id e.rightAdjoint)))

theorem pairing_restrict_right_adjoint {S : Scheme} {G H : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S}
    (e : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing G H) (p : G ⟶ G) (d : H ⟶ H)
    (he : CartierDuality.SheafBlocks.Construction.Schemes.ProjectorsAdjoint e p d) (ell : G ⟶ H) (r : G ⟶ G)
    (hell : r ≫ ell = ell ≫ d) :
    CartierDuality.SheafBlocks.Construction.Schemes.ProjectorsAdjoint (e.restrict (𝟙 G) ell) p r := by
  apply projectorsAdjoint_of_rightMap
  rw [pairing_restrict_rightAdjoint]
  exact Intertwining.Construction.intertwining_comp r d _ ell e.rightAdjoint hell he.right_map

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SheafPairingAdjoints.Construction
