import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LagrangianDual
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.QuotientRepresentability

/-! # Lagrangian Cokernel Dual -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LagrangianCokernelDual.Construction

noncomputable section

/-! The cokernel of an actual self-annihilating monomorphism is the
Cartier dual of its source, retaining the specified subgroup object. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.QuotientRepresentability.Construction.Schemes

universe u
variable {S : AlgebraicGeometry.Scheme.{u}} {G H : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S}
  (j : H ⟶ G) [Mono j]

def subobjectSheafQuotientCokernelIso : CartierDuality.SheafQuotients.Construction.Schemes.sheafQuotient (Subobject.mk j) ≅ cokernel j :=
  cokernelIsoOfEq (Subobject.underlyingIso_hom_comp_eq_mk j).symm ≪≫
    cokernelEpiComp (Subobject.underlyingIso j).hom j

variable (e : CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing G G) (he : e.IsPerfect)
  (hH : CartierDuality.SheafQuotients.Construction.Schemes.sheafAnnihilator e (Subobject.mk j) = Subobject.mk j)
  [IsIso (CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (cokernel j))]

def lagrangianCokernelDualIso : cokernel j ≅ CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf H := by
  let eQ := subobjectSheafQuotientCokernelIso j
  have : IsIso (CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation (CartierDuality.SheafQuotients.Construction.Schemes.sheafQuotient (Subobject.mk j))) :=
    CartierDuality.SheafEvaluation.Construction.Schemes.sheafBidualEvaluation_isIso_of_iso eQ
  exact eQ.symm ≪≫ LagrangianDual.Construction.lagrangianQuotientDualIso e (Subobject.mk j) he hH ≪≫
    (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).mapIso (Subobject.underlyingIso j).symm.op

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LagrangianCokernelDual.Construction
