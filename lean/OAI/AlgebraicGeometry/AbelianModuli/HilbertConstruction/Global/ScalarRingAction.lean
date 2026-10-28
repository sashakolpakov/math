import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleScalars

/-! # Scalar Ring Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ScalarRingAction

noncomputable section

/-! Global regular functions act on every module sheaf by a ring homomorphism into its endomorphism ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def globalModuleScalarRingHom {X : Scheme.{u}} (M : X.Modules) : Γ(X, ⊤) →+* End M where
  toFun := ModuleScalars.globalModuleScalar M
  map_one' := by
    apply Scheme.Modules.hom_ext
    intro U
    apply ConcreteCategory.hom_ext
    intro m
    change X.presheaf.map U.leTop.op 1 • m = m
    rw [map_one, one_smul]
  map_zero' := by
    apply Scheme.Modules.hom_ext
    intro U
    apply ConcreteCategory.hom_ext
    intro m
    change X.presheaf.map U.leTop.op 0 • m = 0
    rw [map_zero, zero_smul]
  map_add' r s := by
    apply Scheme.Modules.hom_ext
    intro U
    apply ConcreteCategory.hom_ext
    intro m
    change X.presheaf.map U.leTop.op (r + s) • m =
      X.presheaf.map U.leTop.op r • m + X.presheaf.map U.leTop.op s • m
    rw [map_add, add_smul]
  map_mul' r s := by
    apply Scheme.Modules.hom_ext
    intro U
    apply ConcreteCategory.hom_ext
    intro m
    change X.presheaf.map U.leTop.op (r * s) • m =
      X.presheaf.map U.leTop.op r • (X.presheaf.map U.leTop.op s • m)
    rw [map_mul, mul_smul]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ScalarRingAction
