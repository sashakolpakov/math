import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactorizationPointCondition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactorizationIsomorphismParameter

/-! # Isomorphic Factorization Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsomorphicFactorizationPoints

noncomputable section

/-! Points of the constructed quasi-projective locus are exactly original parameter maps admitting a factorization with isomorphic projection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left] {X P Z A : Over M.left}
variable [IsProper X.hom] [Flat X.hom] [IsProper A.hom]
variable (j : Z ⟶ P) [IsClosedImmersion j.left] (i : X ⟶ P) (p : Z ⟶ A)

def isomorphicFactorizationPointEquiv (T : Over S) :
    (T ⟶ FactorizationIsomorphismParameter.factorizationIsomorphismParameter M j i p) ≃
      {c : T ⟶ M // FactorizationPointCondition.HasIsomorphicFactorization j i p c.left} :=
  (FactorizationIsomorphismParameter.factorizationIsomorphismParameterPointEquiv M j i p T).trans
    (((Proper.FactorizationParameter.properFactorizationParameterPointEquiv M j i T).subtypeEquiv
      (fun c => (FactorizationPointCondition.factorizationPointLift_condition_iff M j i p c).symm)).trans
        (Equiv.subtypeSubtypeEquivSubtype (fun h => h.existsUnique)))

theorem isomorphicFactorizationPointEquiv_val (T : Over S)
    (y : T ⟶ FactorizationIsomorphismParameter.factorizationIsomorphismParameter M j i p) :
    (isomorphicFactorizationPointEquiv M j i p T y).val =
      (y ≫ FactorizationIsomorphismParameter.factorizationIsomorphismParameterInclusion M j i p) ≫
        Proper.FactorizationParameter.properFactorizationParameterInclusion M j i := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsomorphicFactorizationPoints
