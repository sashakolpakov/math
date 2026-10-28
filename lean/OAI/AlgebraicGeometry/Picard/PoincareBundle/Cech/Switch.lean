import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentSwitch

/-! # Switch -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Switch

noncomputable section

/-!
# A gluing isomorphism on the affine kernel pair gives a tensor switch
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (M : ModuleCat.{u} S)

/-- A genuine isomorphism of the two pullback modules, in tensor coordinates. -/
def gluingAddEquiv (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M) :
    S ⊗[R] (restrictScalars (algebraMap R S)).obj M ≃+
      S ⊗[R] (restrictScalars (algebraMap R S)).obj M :=
  (ModuleModels.firstModel R S M).symm.trans
    (σ.toLinearEquiv.toAddEquiv.trans (ModuleModels.secondModel R S M))

/-- Base scalars act identically through the two affine kernel-pair projections. -/
theorem gluingAddEquiv_smul (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M)
    (r : R) (z : S ⊗[R] (restrictScalars (algebraMap R S)).obj M) :
    gluingAddEquiv R S M σ (r • z) = r • gluingAddEquiv R S M σ z := by
  rw [← IsScalarTower.algebraMap_smul S r z]
  change ModuleModels.secondModel R S M
    (σ.hom ((ModuleModels.firstModel R S M).symm (algebraMap R S r • z))) = _
  rw [ModuleModels.firstModel_symm_smul, ← ModuleModels.projection_base_eq]
  erw [map_smul, ModuleModels.secondModel_first_smul]
  exact IsScalarTower.algebraMap_smul S r _

/-- The gluing isomorphism is R-linear in these tensor coordinates. -/
def gluingSwitch (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M) :
    S ⊗[R] (restrictScalars (algebraMap R S)).obj M ≃ₗ[R]
      S ⊗[R] (restrictScalars (algebraMap R S)).obj M where
  __ := gluingAddEquiv R S M σ
  map_smul' := gluingAddEquiv_smul R S M σ

/-- Scalar multiplication on a module before extension moves to its projection ring. -/
theorem extension_tmul_smul (a : S →+* S ⊗[R] S) (x : S ⊗[R] S) (s : S) (m : M) :
    (x ⊗ₜ[S,a] (s • m) : (extendScalars a).obj M) =
      (a s * x) ⊗ₜ[S,a] m := by
  exact TensorProduct.tmul_smul (R := S) s
    (show (restrictScalars a).obj (of (S ⊗[R] S) (S ⊗[R] S)) from x) m

/-- A gluing isomorphism exchanges the two S-actions in the tensor model. -/
theorem gluingSwitch_second_smul (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M)
    (s t : S) (m : (restrictScalars (algebraMap R S)).obj M) :
    gluingSwitch R S M σ (t ⊗ₜ[R] (s • m)) =
      s • gluingSwitch R S M σ (t ⊗ₜ[R] m) := by
  change ModuleModels.secondModel R S M (σ.hom ((ModuleModels.firstModel R S M).symm (t ⊗ₜ[R] (s • m)))) =
    s • ModuleModels.secondModel R S M (σ.hom ((ModuleModels.firstModel R S M).symm (t ⊗ₜ[R] m)))
  erw [ModuleModels.firstModel_symm_tmul, ModuleModels.firstModel_symm_tmul, extension_tmul_smul,
    ← ModuleCat.ExtendScalars.smul_tmul, map_smul, ModuleModels.secondModel_first_smul]
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Switch
