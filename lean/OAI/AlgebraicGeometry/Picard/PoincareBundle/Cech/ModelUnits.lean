import OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.ExtensionUnits
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels

/-! # Model Units -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModelUnits

noncomputable section

/-!
# Unit generators in the two affine Čech tensor models
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.ExtensionUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (M : ModuleCat.{u} S)

theorem firstModel_symm_unit (m : M) :
    (ModuleModels.firstModel R S M).symm
      ((1 : S) ⊗ₜ[R] (show (restrictScalars (algebraMap R S)).obj M from m)) =
        Scalar.ExtensionUnits.unit (ModuleModels.firstMap R S) M m :=
  ModuleModels.firstModel_symm_tmul R S M 1 m

theorem secondModel_unit (m : M) :
    ModuleModels.secondModel R S M (Scalar.ExtensionUnits.unit (ModuleModels.secondMap R S) M m) =
      (1 : S) ⊗ₜ[R] (show (restrictScalars (algebraMap R S)).obj M from m) := by
  have h := ModuleModels.secondModel_tmul R S M 1 1 m
  have hs := one_smul S (show (restrictScalars (algebraMap R S)).obj M from m)
  exact h.trans (congrArg (fun x : (restrictScalars (algebraMap R S)).obj M =>
    (1 : S) ⊗ₜ[R] x) hs)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModelUnits
