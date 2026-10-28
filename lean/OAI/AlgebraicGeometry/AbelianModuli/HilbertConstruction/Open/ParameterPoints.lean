import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RangeCriterion
import Mathlib.AlgebraicGeometry.Restrict

/-! # Parameter Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ParameterPoints

noncomputable section

/-! Open subschemes represent the condition that a parameter map lands in the specified open subset. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) (U : M.left.Opens)

def openParameterScheme : Over S := Over.mk (U.ι ≫ M.hom)

def openParameterInclusion : openParameterScheme M U ⟶ M := Over.homMk U.ι rfl

instance openParameterInclusion_open : IsOpenImmersion (openParameterInclusion M U).left :=
  inferInstanceAs (IsOpenImmersion U.ι)

def openParameterPointEquiv (T : Over S) :
    (T ⟶ openParameterScheme M U) ≃ {x : T ⟶ M // Set.range x.left ⊆ (U : Set _)} where
  toFun y := ⟨y ≫ openParameterInclusion M U, by
    rintro _ ⟨t, rfl⟩
    exact (y.left t).property⟩
  invFun x := by
    let l : T.left ⟶ U :=
      IsOpenImmersion.lift U.ι x.val.left ((Scheme.Opens.range_ι U).symm ▸ x.property)
    exact Over.homMk l (by
      change l ≫ (U.ι ≫ M.hom) = T.hom
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact x.val.w)
  left_inv y := by
    apply Over.OverMorphism.ext
    apply (cancel_mono U.ι).mp
    exact IsOpenImmersion.lift_fac _ _ _
  right_inv x := by
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact IsOpenImmersion.lift_fac U.ι x.val.left _

theorem openParameterPointEquiv_val (T : Over S) (y : T ⟶ openParameterScheme M U) :
    (openParameterPointEquiv M U T y).val = y ≫ openParameterInclusion M U := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ParameterPoints
