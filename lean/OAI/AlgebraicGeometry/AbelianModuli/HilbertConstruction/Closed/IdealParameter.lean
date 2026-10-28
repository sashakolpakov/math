import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ImmersionFactorization

/-! # Ideal Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.IdealParameter

noncomputable section

/-! An ideal on a parameter scheme defines a closed parameter scheme with its exact points on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) (I : M.left.IdealSheafData)

def closedIdealParameter : Over S := Over.mk (I.subschemeι ≫ M.hom)

def closedIdealParameterInclusion : closedIdealParameter M I ⟶ M :=
  Over.homMk I.subschemeι rfl

instance closedIdealParameterInclusion_closed :
    IsClosedImmersion (closedIdealParameterInclusion M I).left :=
  inferInstanceAs (IsClosedImmersion I.subschemeι)

def closedIdealParameterPointEquiv (T : Over S) :
    (T ⟶ closedIdealParameter M I) ≃ {c : T ⟶ M // I.comap c.left = ⊥} where
  toFun y := ⟨y ≫ closedIdealParameterInclusion M I, by
    rw [ConditionIdeals.ideal_comap_eq_bot_iff]
    change I ≤ (y.left ≫ I.subschemeι).ker
    exact I.ker_subschemeι.symm.le.trans (Scheme.Hom.le_ker_comp _ _)⟩
  invFun c := by
    have h : I.subschemeι.ker ≤ c.val.left.ker :=
      I.ker_subschemeι.le.trans ((ConditionIdeals.ideal_comap_eq_bot_iff I c.val.left).mp c.property)
    let l := IsClosedImmersion.lift I.subschemeι c.val.left h
    exact Over.homMk l (by
      change l ≫ (I.subschemeι ≫ M.hom) = T.hom
      rw [← Category.assoc, IsClosedImmersion.lift_fac]
      exact c.val.w)
  left_inv y := by
    apply Over.OverMorphism.ext
    apply (cancel_mono I.subschemeι).mp
    exact IsClosedImmersion.lift_fac _ _ _
  right_inv c := by
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact IsClosedImmersion.lift_fac I.subschemeι c.val.left _

theorem closedIdealParameterPointEquiv_val (T : Over S) (y : T ⟶ closedIdealParameter M I) :
    (closedIdealParameterPointEquiv M I T y).val = y ≫ closedIdealParameterInclusion M I := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.IdealParameter
