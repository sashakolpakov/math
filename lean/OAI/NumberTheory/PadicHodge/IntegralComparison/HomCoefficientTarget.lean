import OAI.NumberTheory.PadicHodge.IntegralComparison.HomPresheafDualFrame

/-! # Hom Coefficient Target -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.HomCoefficientTarget

noncomputable section

/-! Postcomposition of a Hom coefficient diagram preserves its literal
evaluation maps, including a change of the target diagram by an isomorphism. -/
open _root_.CategoryTheory
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type v} [Category C] (R : Type u) [CommRing R]
  (M : ModuleCat.{u} R)

def map {P Q : C ⥤ ModuleCat.{u} R} (a : P ⟶ Q) :
    HomCoefficientFunctor.homPresheaf R P M ⟶ HomCoefficientFunctor.homPresheaf R Q M where
  app c := ModuleCat.ofHom
    { toFun φ := (a.app c).hom.comp φ
      map_add' φ ψ := by ext x; simp
      map_smul' r φ := by ext x; simp }
  naturality c d f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change M →ₗ[R] P.obj c at φ
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom (a.naturality f) (φ x)

def iso {P Q : C ⥤ ModuleCat.{u} R} (a : P ≅ Q) :
    HomCoefficientFunctor.homPresheaf R P M ≅ HomCoefficientFunctor.homPresheaf R Q M where
  hom := map R M a.hom
  inv := map R M a.inv
  hom_inv_id := by
    apply NatTrans.ext
    funext c
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change M →ₗ[R] P.obj c at φ
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom (congrArg (fun b => b.app c) a.hom_inv_id) (φ x)
  inv_hom_id := by
    apply NatTrans.ext
    funext c
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change M →ₗ[R] Q.obj c at φ
    apply LinearMap.ext
    intro x
    exact ConcreteCategory.congr_hom (congrArg (fun b => b.app c) a.inv_hom_id) (φ x)

theorem evaluation {P Q : C ⥤ ModuleCat.{u} R} (a : P ⟶ Q) (x : M) :
    map R M a ≫ HomPresheafDualFrame.evaluation R Q M x =
      HomPresheafDualFrame.evaluation R P M x ≫ a := by
  apply NatTrans.ext
  funext c
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.HomCoefficientTarget
