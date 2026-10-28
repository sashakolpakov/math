import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorFrameSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorComultiplication

/-! # Global Tensor Section Coherence -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalTensorSectionCoherence

noncomputable section

/-! Associators and unitors on actual pure tensor global sections. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite
universe u

local instance globalTensorCoherenceMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

theorem topSectionHom_injective {X : Scheme.{u}} (M : X.Modules) :
    Function.Injective (SectionIdentities.Scheme.Modules.topSectionHom M) := by
  intro x y h
  have ha := congrArg (fun f => f.val.app (op ⊤) (show Γ(X, ⊤) from 1)) h
  change (TensorFrameSections.poleTopSectionHom M x).val.app (op ⊤) _ =
    (TensorFrameSections.poleTopSectionHom M y).val.app (op ⊤) _ at ha
  simpa only [TensorFrameSections.poleTopSectionHom_app_top_apply_one] using ha

theorem associator_tensorSection_top {X : Scheme.{u}} (M N P : X.Modules)
    (x : Γ(M, ⊤)) (y : Γ(N, ⊤)) (z : Γ(P, ⊤)) :
    (α_ M N P).hom.val.app (op ⊤)
        (TensorSections.tensorSection (M ⊗ N) P ⊤ (TensorSections.tensorSection M N ⊤ x y) z) =
      TensorSections.tensorSection M (N ⊗ P) ⊤ x (TensorSections.tensorSection N P ⊤ y z) := by
  apply topSectionHom_injective (M ⊗ (N ⊗ P))
  rw [← TensorFrameSections.topSectionHom_comp]
  simp only [TensorFrameSections.topSectionHom_tensorSection]
  exact TensorComultiplication.tensorComulHom_assoc (D := X.Modules) (A := M) (B := N) (C := P)
    (O := Invertible.Scheme.Modules.unitObj X) (SectionIdentities.Scheme.Modules.topSectionHom M x)
    (SectionIdentities.Scheme.Modules.topSectionHom N y) (SectionIdentities.Scheme.Modules.topSectionHom P z)
    (TensorSections.unitObjTensorIso X).inv
    (TensorComultiplication.tensorIso_inv_coassoc (D := X.Modules) (O := Invertible.Scheme.Modules.unitObj X)
      (TensorSections.unitObjTensorIso X) (TensorSections.unitObjTensorIso_hom_assoc X))

theorem topSectionHom_monoidalUnitSection (X : Scheme.{u}) :
    SectionIdentities.Scheme.Modules.topSectionHom (𝟙_ X.Modules) (TensorSections.monoidalUnitSection X) =
      (TensorSections.monoidalUnitObjIso X).inv := by
  apply TensorFrameSections.poleUnitObj_hom_ext_top
  change (TensorFrameSections.poleTopSectionHom _ _).val.app (op ⊤) _ = _
  rw [TensorFrameSections.poleTopSectionHom_app_top_apply_one]
  rfl

theorem leftUnitor_tensorSection_top {X : Scheme.{u}} (M : X.Modules)
    (x : Γ(M, ⊤)) :
    (λ_ M).hom.val.app (op ⊤)
      (TensorSections.tensorSection (𝟙_ X.Modules) M ⊤ (TensorSections.monoidalUnitSection X) x) = x := by
  apply topSectionHom_injective M
  rw [← TensorFrameSections.topSectionHom_comp, TensorFrameSections.topSectionHom_tensorSection,
    topSectionHom_monoidalUnitSection]
  simp only [TensorSections.unitObjTensorIso, Iso.trans_inv, tensorIso_inv, Iso.symm_inv,
    Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id, id_tensorHom,
    leftUnitor_naturality]
  simp only [Iso.inv_hom_id_assoc]

theorem rightUnitor_tensorSection_top {X : Scheme.{u}} (M : X.Modules)
    (x : Γ(M, ⊤)) :
    (ρ_ M).hom.val.app (op ⊤)
      (TensorSections.tensorSection M (𝟙_ X.Modules) ⊤ x (TensorSections.monoidalUnitSection X)) = x := by
  apply topSectionHom_injective M
  rw [← TensorFrameSections.topSectionHom_comp, TensorFrameSections.topSectionHom_tensorSection,
    topSectionHom_monoidalUnitSection]
  simp only [TensorSections.unitObjTensorIso, Iso.trans_inv, tensorIso_inv, Iso.symm_inv,
    Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id, tensorHom_id,
    rightUnitor_naturality, ← unitors_equal]
  simp only [Iso.inv_hom_id_assoc]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalTensorSectionCoherence
