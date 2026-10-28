import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionModules

/-! # Open Function Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionScalars

noncomputable section

/-! Multiplication by a local function is linear over functions on a containing open and commutes with restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

def relativeOpenFunctionScalar (V W : X.Opens) (h : W ≤ V) (a : Γ(X, W)) :
    End (OpenFunctionModules.relativeOpenFunctionModule V W h) :=
  ModuleCat.ofHom (X := OpenFunctionModules.relativeOpenFunctionModule V W h) (Y := OpenFunctionModules.relativeOpenFunctionModule V W h) {
    toFun := @Mul.mul Γ(X, W) inferInstance a
    map_add' := mul_add a
    map_smul' := fun r x => by
      change @Mul.mul Γ(X, W) inferInstance a
          (@Mul.mul Γ(X, W) inferInstance (X.presheaf.map (homOfLE h).op r) x) =
        @Mul.mul Γ(X, W) inferInstance (X.presheaf.map (homOfLE h).op r)
          (@Mul.mul Γ(X, W) inferInstance a x)
      exact mul_left_comm a (X.presheaf.map (homOfLE h).op r) x }

theorem relativeOpenFunctionScalar_restriction (V : X.Opens) {W Z : X.Opens}
    (hW : W ≤ V) (hZ : Z ≤ V) (h : Z ≤ W) (a : Γ(X, W)) :
    relativeOpenFunctionScalar V W hW a ≫ OpenFunctionModules.relativeOpenFunctionRestriction V hW hZ h =
      OpenFunctionModules.relativeOpenFunctionRestriction V hW hZ h ≫
        relativeOpenFunctionScalar V Z hZ (X.presheaf.map (homOfLE h).op a) := by
  apply ModuleCat.hom_ext
  ext x
  exact (X.presheaf.map (homOfLE h).op).hom.map_mul a x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.OpenFunctionScalars
