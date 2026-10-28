import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Switch

/-! # Model Linearity -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModelLinearity

noncomputable section

/-!
# Base-ring linear tensor models for affine Čech pullbacks

These equivalences allow the Čech diagrams to be extended by another
tensor factor when checking the three-factor cocycle.
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Switch

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (M : ModuleCat.{u} S)

/-- The first projection pullback in R-linear tensor coordinates. -/
def firstLinearModel :
    (restrictScalars (algebraMap R (S ⊗[R] S))).obj (ModuleModels.firstPullback R S M) ≃ₗ[R]
      S ⊗[R] (restrictScalars (algebraMap R S)).obj M where
  __ := ModuleModels.firstModel R S M
  map_smul' r z := by
    change ModuleModels.firstModel R S M (algebraMap R (S ⊗[R] S) r •
      (show ModuleModels.firstPullback R S M from z)) = r • ModuleModels.firstModel R S M z
    have h : algebraMap R (S ⊗[R] S) r = ModuleModels.secondMap R S (algebraMap R S r) :=
      (Algebra.TensorProduct.includeRight.commutes r).symm
    rw [h, ModuleModels.firstModel_second_smul]
    exact IsScalarTower.algebraMap_smul S r _

/-- The second projection pullback in R-linear tensor coordinates. -/
def secondLinearModel :
    (restrictScalars (algebraMap R (S ⊗[R] S))).obj (ModuleModels.secondPullback R S M) ≃ₗ[R]
      S ⊗[R] (restrictScalars (algebraMap R S)).obj M where
  __ := ModuleModels.secondModel R S M
  map_smul' r z := by
    change ModuleModels.secondModel R S M (algebraMap R (S ⊗[R] S) r •
      (show ModuleModels.secondPullback R S M from z)) = r • ModuleModels.secondModel R S M z
    have h : algebraMap R (S ⊗[R] S) r = ModuleModels.firstMap R S (algebraMap R S r) :=
      ((Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S).commutes r).symm
    rw [h, ModuleModels.secondModel_first_smul]
    exact IsScalarTower.algebraMap_smul S r _

/-- In R-linear coordinates the actual gluing map is precisely the tensor switch. -/
theorem gluingSwitch_factorization (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M) :
    (Switch.gluingSwitch R S M σ).toLinearMap =
      (secondLinearModel R S M).toLinearMap ∘ₗ
        ((restrictScalars (algebraMap R (S ⊗[R] S))).map σ.hom).hom ∘ₗ
        (firstLinearModel R S M).symm.toLinearMap := rfl

/-- Extending gluing by one tensor factor gives the switch on the last two factors. -/
theorem nextSwitch_factorization (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M) :
    DescentSwitch.nextSwitch R S ((restrictScalars (algebraMap R S)).obj M)
        (Switch.gluingSwitch R S M σ) =
      TensorProduct.map (LinearMap.id : S →ₗ[R] S) (secondLinearModel R S M).toLinearMap ∘ₗ
        TensorProduct.map (LinearMap.id : S →ₗ[R] S)
          ((restrictScalars (algebraMap R (S ⊗[R] S))).map σ.hom).hom ∘ₗ
        TensorProduct.map (LinearMap.id : S →ₗ[R] S)
          (firstLinearModel R S M).symm.toLinearMap := by
  apply TensorProduct.ext
  ext s z
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModelLinearity
