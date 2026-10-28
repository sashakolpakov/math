import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorFrameSections

/-! # Sheafification Tensor Associator -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.SheafificationTensorAssociator

noncomputable section

/-! Associativity of pure sections in the sheafified tensor product over any open. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite
universe u

local instance associatorSectionsMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Projective.Monoidal.Scheme.Modules.monoidalCategory X
local instance associatorSectionsSheafMonoidal (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules X.ringCatSheaf) :=
  Projective.Monoidal.Scheme.Modules.monoidalCategory X
local instance associatorSectionsLocalization (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization
      (OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj)) := by
  change (PresheafOfModules.sheafification
    (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
      X.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat X).obj)).IsLocalization
    (OfModulesMonoidal.PresheafOfModules.sheafificationW
      (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
        X.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat X).obj))
  infer_instance
local instance associatorSectionsWMonoidal (X : Scheme.{u}) :
    (OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj)).IsMonoidal := by
  change (OfModulesMonoidal.PresheafOfModules.sheafificationW
    (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat,
      X.ringCatSheaf.property⟩ : TopCat.Sheaf RingCat X).obj)).IsMonoidal
  infer_instance
local instance associatorSectionsSheafificationMonoidal (X : Scheme.{u}) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).Monoidal :=
  inferInstanceAs ((Localization.Monoidal.toMonoidalCategory
    (L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
    (W := OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj))
    (Iso.refl _)).Monoidal)

theorem sheafification_map_associator_unit {X : Scheme.{u}}
    (A B C : X.PresheafOfModules) (U : X.Opens)
    (x : A.obj (op U)) (y : B.obj (op U)) (z : C.obj (op U)) :
    let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
    (L.map (α_ A B C).hom).val.app (op U)
      ((adj.unit.app ((A ⊗ B) ⊗ C)).app (op U)
        ((show (A ⊗ B).obj (op U) from x ⊗ₜ y) ⊗ₜ z)) =
      (adj.unit.app (A ⊗ (B ⊗ C))).app (op U)
        (x ⊗ₜ (show (B ⊗ C).obj (op U) from y ⊗ₜ z)) := by
  dsimp only
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have h := adj.unit.naturality (α_ A B C).hom
  have hu := congrArg (fun f => f.app (op U)
    ((show (A ⊗ B).obj (op U) from x ⊗ₜ y) ⊗ₜ z)) h
  exact hu.symm

theorem sheafification_delta_left_tmul {X : Scheme.{u}}
    (A B C : X.PresheafOfModules) (U : X.Opens)
    (x : A.obj (op U)) (y : B.obj (op U)) (z : C.obj (op U)) :
    let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
    ((Functor.OplaxMonoidal.δ L A B ⊗ₘ 𝟙 (L.obj C)).val.app (op U))
      ((Functor.OplaxMonoidal.δ L (A ⊗ B) C).val.app (op U)
        ((adj.unit.app ((A ⊗ B) ⊗ C)).app (op U)
          ((show (A ⊗ B).obj (op U) from x ⊗ₜ y) ⊗ₜ z))) =
      TensorSections.tensorSection (L.obj A ⊗ L.obj B) (L.obj C) U
        (TensorSections.tensorSection (L.obj A) (L.obj B) U
          ((adj.unit.app A).app (op U) x) ((adj.unit.app B).app (op U) y))
        ((adj.unit.app C).app (op U) z) := by
  dsimp only
  rw [TensorSections.sheafification_δ_unit_tmul_eq_tensorSection, TensorFrameSections.tensorSection_map,
    TensorSections.sheafification_δ_unit_tmul_eq_tensorSection]
  rfl

theorem sheafification_delta_right_tmul {X : Scheme.{u}}
    (A B C : X.PresheafOfModules) (U : X.Opens)
    (x : A.obj (op U)) (y : B.obj (op U)) (z : C.obj (op U)) :
    let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
    ((𝟙 (L.obj A) ⊗ₘ Functor.OplaxMonoidal.δ L B C).val.app (op U))
      ((Functor.OplaxMonoidal.δ L A (B ⊗ C)).val.app (op U)
        ((adj.unit.app (A ⊗ (B ⊗ C))).app (op U)
          (x ⊗ₜ (show (B ⊗ C).obj (op U) from y ⊗ₜ z)))) =
      TensorSections.tensorSection (L.obj A) (L.obj B ⊗ L.obj C) U
        ((adj.unit.app A).app (op U) x)
        (TensorSections.tensorSection (L.obj B) (L.obj C) U
          ((adj.unit.app B).app (op U) y) ((adj.unit.app C).app (op U) z)) := by
  dsimp only
  rw [TensorSections.sheafification_δ_unit_tmul_eq_tensorSection, TensorFrameSections.tensorSection_map,
    TensorSections.sheafification_δ_unit_tmul_eq_tensorSection]
  rfl

theorem sheafification_associator_tensorSection {X : Scheme.{u}}
    (A B C : X.PresheafOfModules) (U : X.Opens)
    (x : A.obj (op U)) (y : B.obj (op U)) (z : C.obj (op U)) :
    let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
    (α_ (L.obj A) (L.obj B) (L.obj C)).hom.val.app (op U)
      (TensorSections.tensorSection (L.obj A ⊗ L.obj B) (L.obj C) U
        (TensorSections.tensorSection (L.obj A) (L.obj B) U
          ((adj.unit.app A).app (op U) x) ((adj.unit.app B).app (op U) y))
        ((adj.unit.app C).app (op U) z)) =
      TensorSections.tensorSection (L.obj A) (L.obj B ⊗ L.obj C) U
        ((adj.unit.app A).app (op U) x)
        (TensorSections.tensorSection (L.obj B) (L.obj C) U
          ((adj.unit.app B).app (op U) y) ((adj.unit.app C).app (op U) z)) := by
  dsimp only
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have h := Functor.OplaxMonoidal.associativity L A B C
  simp only [← tensorHom_id, ← id_tensorHom] at h
  have hu := congrArg (fun f => f.val.app (op U)
    ((adj.unit.app ((A ⊗ B) ⊗ C)).app (op U)
      ((show (A ⊗ B).obj (op U) from x ⊗ₜ y) ⊗ₜ z))) h
  conv_lhs at hu =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  conv_rhs at hu =>
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rw [sheafification_delta_left_tmul, sheafification_map_associator_unit,
    sheafification_delta_right_tmul] at hu
  exact hu

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.SheafificationTensorAssociator
