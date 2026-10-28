import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorFrameSections

/-! # Tensor Triple Naturality -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorTripleNaturality

noncomputable section

/-! Tensor triples and associators commute with morphisms on their three factors. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite
universe u
local instance tensorTripleMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

theorem tensorSection_map_left_three {X : Scheme.{u}}
    {A B C A' B' C' : X.Modules} (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C')
    (U : X.Opens) (x : Γ(A, U)) (y : Γ(B, U)) (z : Γ(C, U)) :
    ((f ⊗ₘ g) ⊗ₘ h).val.app (op U)
      (TensorSections.tensorSection (A ⊗ B) C U (TensorSections.tensorSection A B U x y) z) =
      TensorSections.tensorSection (A' ⊗ B') C' U
        (TensorSections.tensorSection A' B' U (f.val.app (op U) x) (g.val.app (op U) y))
        (h.val.app (op U) z) := by
  rw [TensorFrameSections.tensorSection_map, TensorFrameSections.tensorSection_map]

theorem tensorSection_map_right_three {X : Scheme.{u}}
    {A B C A' B' C' : X.Modules} (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C')
    (U : X.Opens) (x : Γ(A, U)) (y : Γ(B, U)) (z : Γ(C, U)) :
    (f ⊗ₘ (g ⊗ₘ h)).val.app (op U)
      (TensorSections.tensorSection A (B ⊗ C) U x (TensorSections.tensorSection B C U y z)) =
      TensorSections.tensorSection A' (B' ⊗ C') U (f.val.app (op U) x)
        (TensorSections.tensorSection B' C' U (g.val.app (op U) y) (h.val.app (op U) z)) := by
  rw [TensorFrameSections.tensorSection_map, TensorFrameSections.tensorSection_map]

theorem associator_tensorSection_transport {X : Scheme.{u}}
    {A B C A' B' C' : X.Modules} (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C')
    (U : X.Opens) (x : Γ(A, U)) (y : Γ(B, U)) (z : Γ(C, U))
    (ha : (α_ A B C).hom.val.app (op U)
      (TensorSections.tensorSection (A ⊗ B) C U (TensorSections.tensorSection A B U x y) z) =
      TensorSections.tensorSection A (B ⊗ C) U x (TensorSections.tensorSection B C U y z)) :
    (α_ A' B' C').hom.val.app (op U)
      (TensorSections.tensorSection (A' ⊗ B') C' U
        (TensorSections.tensorSection A' B' U (f.val.app (op U) x) (g.val.app (op U) y))
        (h.val.app (op U) z)) =
      TensorSections.tensorSection A' (B' ⊗ C') U (f.val.app (op U) x)
        (TensorSections.tensorSection B' C' U (g.val.app (op U) y) (h.val.app (op U) z)) := by
  have hn := associator_naturality f g h
  have hu := congrArg (fun k => k.val.app (op U)
    (TensorSections.tensorSection (A ⊗ B) C U (TensorSections.tensorSection A B U x y) z)) hn
  conv_lhs at hu =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  conv_rhs at hu =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rw [tensorSection_map_left_three, ha, tensorSection_map_right_three] at hu
  exact hu

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorTripleNaturality
