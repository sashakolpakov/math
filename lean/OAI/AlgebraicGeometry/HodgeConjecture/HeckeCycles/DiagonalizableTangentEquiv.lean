import OAI.RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents

/-! # Diagonalizable Tangent Equiv -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalizableTangentEquiv.CM

noncomputable section

/-! Every tangent point of a diagonalizable group has the form
1 + epsilon times an additive character, on the actual dual-number test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents

variable {k M : Type} [Field k] [CommGroup M]

theorem character_fst (φ : M →* DualNumber k)
    (h : AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k ≫ RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.pointEquiv φ = 1) (m : M) : (φ m).fst = 1 := by
  have hh := congrArg Over.Hom.left h
  change Spec.map (CommRingCat.ofHom (AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction k)) ≫
    Spec.map (CommRingCat.ofHom (MonoidAlgebra.lift k (DualNumber k) M φ).toRingHom) = _ at hh
  rw [← Spec.map_comp, Hom.one_def, Over.comp_left, one_spec_asOver_spec_left] at hh
  have hh' : Spec.map (CommRingCat.ofHom
      ((AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction k).comp (MonoidAlgebra.lift k (DualNumber k) M φ).toRingHom)) =
      Spec.map (CommRingCat.ofHom (Bialgebra.counitAlgHom k (MonoidAlgebra k M)).toRingHom) :=
    hh.trans (Category.id_comp _)
  have ha := Spec.map_injective hh'
  have hm := ConcreteCategory.congr_hom ha (MonoidAlgebra.single m 1)
  change ((MonoidAlgebra.lift k (DualNumber k) M φ) (MonoidAlgebra.single m 1)).fst = _ at hm
  simpa using hm

def additiveCharacter (φ : M →* DualNumber k) (h : ∀ m, (φ m).fst = 1) : Additive M →+ k where
  toFun m := (φ m.toMul).snd
  map_zero' := by simp
  map_add' a b := by
    change (φ (a.toMul * b.toMul)).snd = _
    rw [map_mul]
    change (φ a.toMul).fst * (φ b.toMul).snd +
      (φ a.toMul).snd * (φ b.toMul).fst = _
    rw [h, h, one_mul, mul_one, add_comm]

theorem character_additiveCharacter (φ : M →* DualNumber k) (h : ∀ m, (φ m).fst = 1) :
    RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.character (additiveCharacter φ h) = φ := by
  apply MonoidHom.ext
  intro m
  apply TrivSqZeroExt.ext
  · exact (h m).symm
  · rfl

def tangentEquiv : (Additive M →+ k) ≃
    {p : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.groupScheme (M := M) // AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k ≫ p = 1} where
  toFun χ := ⟨RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.point χ, RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.point_reduction χ⟩
  invFun p := additiveCharacter (RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.pointEquiv.symm p.val)
    (character_fst _ (by simpa using p.property))
  left_inv χ := by
    apply AddMonoidHom.ext
    intro m
    change ((RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.pointEquiv.symm (RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.pointEquiv (RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.character χ))) m.toMul).snd = χ m
    rw [MulEquiv.symm_apply_apply]
    rfl
  right_inv p := by
    apply Subtype.ext
    change RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.pointEquiv (RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.character (additiveCharacter _ _)) = p.val
    rw [character_additiveCharacter, MulEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DiagonalizableTangentEquiv.CM
