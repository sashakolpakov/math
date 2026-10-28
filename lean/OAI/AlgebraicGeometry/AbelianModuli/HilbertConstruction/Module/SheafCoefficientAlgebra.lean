import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ScalarRingAction
import Mathlib.Algebra.Algebra.Basic

/-! # Sheaf Coefficient Algebra -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SheafCoefficientAlgebra

noncomputable section

/-! A genuine coefficient map to global regular functions makes every module-sheaf endomorphism ring a coefficient algebra. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v

abbrev moduleSheafCoefficientAlgebra {K : Type v} [CommRing K] {X : Scheme.{u}}
    (c : K →+* Γ(X, ⊤)) (M : X.Modules) : Algebra K (End M) :=
  ((Global.ScalarRingAction.globalModuleScalarRingHom M).comp c).toAlgebra' (fun k φ =>
    (Global.ModuleScalars.globalModuleScalar_natural (c k) φ).symm)

theorem moduleSheafCoefficientAlgebra_map {K : Type v} [CommRing K] {X : Scheme.{u}}
    (c : K →+* Γ(X, ⊤)) (M : X.Modules) (k : K) :
    @algebraMap K (End M) _ _ (moduleSheafCoefficientAlgebra c M) k =
      Global.ModuleScalars.globalModuleScalar M (c k) := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SheafCoefficientAlgebra
