import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionScalars

/-! # Open Function Units -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionUnits

noncomputable section

/-! Restricting regular functions is a linear map from the containing open's free rank-one module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

def relativeOpenFunctionUnitMap (V W : X.Opens) (h : W ≤ V) :
    Γ(X, V) →ₗ[Γ(X, V)] OpenFunctionModules.relativeOpenFunctionModule V W h where
  toFun := X.presheaf.map (homOfLE h).op
  map_add' := (X.presheaf.map (homOfLE h).op).hom.map_add
  map_smul' := (X.presheaf.map (homOfLE h).op).hom.map_mul

theorem openFunction_restriction_comp {V W Z : X.Opens} (a : W ≤ V) (b : Z ≤ W) (r : Γ(X, V)) :
    X.presheaf.map (homOfLE b).op (X.presheaf.map (homOfLE a).op r) =
      X.presheaf.map (homOfLE (b.trans a)).op r :=
  (ConcreteCategory.congr_hom (X.presheaf.map_comp (homOfLE a).op (homOfLE b).op) r).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionUnits
