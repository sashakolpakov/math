import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Switch

/-! # Symmetry -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Symmetry

noncomputable section

/-!
# Coordinate transposition and the symmetry law for affine descent
-/

open _root_.CategoryTheory _root_.ModuleCat TensorProduct
open scoped TensorProduct ChangeOfRings

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.ModuleModels OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Switch

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (M : ModuleCat.{u} S)

/-- Swapping the affine coordinates acts semilinearly on the actual pullback module. -/
theorem flipPullback_smul (x : S ⊗[R] S) (z : ModuleModels.secondPullback R S M) :
    ModuleModels.flipPullback R S M (x • z) =
      Algebra.TensorProduct.comm R S S x • ModuleModels.flipPullback R S M z :=
  ExtensionTwist.extensionEquiv_smul (ModuleModels.secondMap R S) (ModuleModels.firstMap R S)
    (Algebra.TensorProduct.comm R S S).toRingEquiv (ModuleModels.flip_second R S) M x z

/-- Coordinate transposition applied to the gluing morphism. -/
def swappedHom (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M) :
    ModuleModels.secondPullback R S M ⟶ ModuleModels.firstPullback R S M :=
  ofHom (X := ModuleModels.secondPullback R S M) (Y := ModuleModels.firstPullback R S M) {
    toFun := fun z => ModuleModels.flipPullback R S M (σ.hom (ModuleModels.flipPullback R S M z))
    map_add' := fun x y => by rw [map_add, map_add, map_add]
    map_smul' := fun x z => by
      erw [flipPullback_smul, map_smul, flipPullback_smul]
      have he : Algebra.TensorProduct.comm R S S (Algebra.TensorProduct.comm R S S x) = x := by
        simpa only [Algebra.TensorProduct.comm_symm] using
          (Algebra.TensorProduct.comm R S S).symm_apply_apply x
      rw [he]
      rfl }

/-- If transposed gluing is inverse gluing, the associated tensor switch is involutive. -/
theorem gluingSwitch_involutive (σ : ModuleModels.firstPullback R S M ≅ ModuleModels.secondPullback R S M)
    (h : swappedHom R S M σ = σ.inv)
    (z : S ⊗[R] (restrictScalars (algebraMap R S)).obj M) :
    Switch.gluingSwitch R S M σ (Switch.gluingSwitch R S M σ z) = z := by
  have hh : σ.hom ≫ swappedHom R S M σ = 𝟙 _ := by rw [h, σ.hom_inv_id]
  have hp := ConcreteCategory.congr_hom hh ((ModuleModels.firstModel R S M).symm z)
  change ModuleModels.firstModel R S M
    (ModuleModels.flipPullback R S M (σ.hom ((ModuleModels.firstModel R S M).symm
      (ModuleModels.firstModel R S M (ModuleModels.flipPullback R S M (σ.hom ((ModuleModels.firstModel R S M).symm z))))))) = z
  rw [AddEquiv.symm_apply_apply]
  change ModuleModels.flipPullback R S M (σ.hom
    (ModuleModels.flipPullback R S M (σ.hom ((ModuleModels.firstModel R S M).symm z)))) =
      (ModuleModels.firstModel R S M).symm z at hp
  rw [hp, AddEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.Symmetry
