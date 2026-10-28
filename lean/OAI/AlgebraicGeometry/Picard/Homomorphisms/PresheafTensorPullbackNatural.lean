import OAI.AlgebraicGeometry.Picard.Homomorphisms.PresheafTensorPullback

/-! # Presheaf Tensor Pullback Natural -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.PresheafTensorPullbackNatural

noncomputable section

/-! Naturality of the tensor comparison for module-presheaf pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

local instance presheafTensorPullbackNaturalLocal1 : MonoidalCategory X.PresheafOfModules := PresheafOfModulesOfCommRing.monoidalCategory
local instance presheafTensorPullbackNaturalLocal2 : MonoidalCategory Y.PresheafOfModules := PresheafOfModulesOfCommRing.monoidalCategory

theorem presheafPushforwardTensorMap_naturality {M M' N N' : X.PresheafOfModules}
    (a : M ⟶ M') (b : N ⟶ N') :
    ((PresheafTensorPullback.Construction.modulePresheafPushforward f).map a ⊗ₘ (PresheafTensorPullback.Construction.modulePresheafPushforward f).map b) ≫
        PresheafTensorPullback.Construction.presheafPushforwardTensorMap f M' N' =
      PresheafTensorPullback.Construction.presheafPushforwardTensorMap f M N ≫ (PresheafTensorPullback.Construction.modulePresheafPushforward f).map (a ⊗ₘ b) := by
  ext1 U
  exact Functor.LaxMonoidal.μ_natural (ModuleCat.restrictScalars (f.app U.unop).hom)
    (a.app (op (f ⁻¹ᵁ U.unop))) (b.app (op (f ⁻¹ᵁ U.unop)))

theorem presheafTensorPullbackComparison_naturality {M M' N N' : Y.PresheafOfModules}
    (a : M ⟶ M') (b : N ⟶ N') :
    (PresheafTensorPullback.Construction.modulePresheafPullback f).map (a ⊗ₘ b) ≫ PresheafTensorPullback.Construction.presheafTensorPullbackComparison f M' N' =
      PresheafTensorPullback.Construction.presheafTensorPullbackComparison f M N ≫
        ((PresheafTensorPullback.Construction.modulePresheafPullback f).map a ⊗ₘ (PresheafTensorPullback.Construction.modulePresheafPullback f).map b) := by
  apply ((PresheafTensorPullback.Construction.modulePresheafAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    PresheafTensorPullback.Construction.presheafTensorPullbackComparison_homEquiv, PresheafTensorPullback.Construction.presheafTensorPullbackComparison_homEquiv]
  rw [← Category.assoc, tensorHom_comp_tensorHom]
  erw [(PresheafTensorPullback.Construction.modulePresheafAdjunction f).unit.naturality a,
    (PresheafTensorPullback.Construction.modulePresheafAdjunction f).unit.naturality b]
  rw [← tensorHom_comp_tensorHom, Category.assoc]
  simp only [CategoryTheory.Functor.comp_map]
  rw [presheafPushforwardTensorMap_naturality]
  simp only [Category.assoc]

def presheafTensorPullbackRightComparison (N : Y.PresheafOfModules) :
    tensorRight N ⋙ PresheafTensorPullback.Construction.modulePresheafPullback f ⟶
      PresheafTensorPullback.Construction.modulePresheafPullback f ⋙ tensorRight ((PresheafTensorPullback.Construction.modulePresheafPullback f).obj N) where
  app M := PresheafTensorPullback.Construction.presheafTensorPullbackComparison f M N
  naturality {M M'} a := by
    have h := presheafTensorPullbackComparison_naturality f a (𝟙 N)
    simp only [CategoryTheory.Functor.map_id, tensorHom_id] at h
    exact h

def presheafTensorPullbackLeftComparison (M : Y.PresheafOfModules) :
    tensorLeft M ⋙ PresheafTensorPullback.Construction.modulePresheafPullback f ⟶
      PresheafTensorPullback.Construction.modulePresheafPullback f ⋙ tensorLeft ((PresheafTensorPullback.Construction.modulePresheafPullback f).obj M) where
  app N := PresheafTensorPullback.Construction.presheafTensorPullbackComparison f M N
  naturality {N N'} b := by
    have h := presheafTensorPullbackComparison_naturality f (𝟙 M) b
    simp only [CategoryTheory.Functor.map_id, id_tensorHom] at h
    exact h

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.PresheafTensorPullbackNatural
