import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.DoubleAnnihilator

/-! # Lagrangian Dual -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LagrangianDual.Construction

noncomputable section

/-! A self-annihilating subgroup under a perfect Cartier pairing has
quotient canonically isomorphic to its actual character sheaf. -/

open _root_.CategoryTheory

universe u
variable {S : AlgebraicGeometry.Scheme.{u}} {G : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S}
  (e : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing G G) (H : Subobject G) (he : e.IsPerfect)
  (hH : CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e H = H)
  [IsIso (CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (CartierDuality.SheafQuotients.Construction.Schemes.sheafQuotient H))]

def lagrangianQuotientDualIso : CartierDuality.SheafQuotients.Construction.Schemes.sheafQuotient H ≅ CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (H : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S) := by
  let a : (H : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S) ≅ CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CartierDuality.SheafQuotients.Construction.Schemes.sheafQuotient H) :=
    eqToIso (congrArg (fun K : Subobject G => (K : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S)) hH.symm) ≪≫
      CartierDuality.SheafQuotients.Construction.Schemes.annihilatorQuotientDualIso e H he
  exact asIso (CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (CartierDuality.SheafQuotients.Construction.Schemes.sheafQuotient H)) ≪≫ (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).mapIso a.op

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LagrangianDual.Construction
