import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.IdealParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FactorizationIdeal

/-! # Factorization Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FactorizationParameter

noncomputable section

/-! Proper-flat closed factorization is represented by a specified closed parameter scheme on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left] {X P Z : Over M.left}
variable [IsProper X.hom] [Flat X.hom] (j : Z ⟶ P) [IsClosedImmersion j.left] (i : X ⟶ P)

def properFactorizationParameter : Over S := Closed.IdealParameter.closedIdealParameter M (FactorizationIdeal.properFactorizationIdeal j i)

def properFactorizationParameterInclusion : properFactorizationParameter M j i ⟶ M :=
  Closed.IdealParameter.closedIdealParameterInclusion M (FactorizationIdeal.properFactorizationIdeal j i)

instance properFactorizationParameterInclusion_closed :
    IsClosedImmersion (properFactorizationParameterInclusion M j i).left :=
  inferInstanceAs (IsClosedImmersion (Closed.IdealParameter.closedIdealParameterInclusion M (FactorizationIdeal.properFactorizationIdeal j i)).left)

def properFactorizationParameterPointEquiv (T : Over S) :
    (T ⟶ properFactorizationParameter M j i) ≃
      {c : T ⟶ M // ∃! h : (Over.pullback c.left).obj X ⟶ (Over.pullback c.left).obj Z,
        h ≫ (Over.pullback c.left).map j = (Over.pullback c.left).map i} :=
  (Closed.IdealParameter.closedIdealParameterPointEquiv M (FactorizationIdeal.properFactorizationIdeal j i) T).trans
    { toFun := fun c => ⟨c.val, (FactorizationIdeal.properFactorizationIdeal_test j i c.val.left).mp c.property⟩
      invFun := fun c => ⟨c.val, (FactorizationIdeal.properFactorizationIdeal_test j i c.val.left).mpr c.property⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }

theorem properFactorizationParameterPointEquiv_val (T : Over S)
    (y : T ⟶ properFactorizationParameter M j i) :
    (properFactorizationParameterPointEquiv M j i T y).val =
      y ≫ properFactorizationParameterInclusion M j i := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FactorizationParameter
