import OAI.AlgebraicGeometry.ComplexMultiplication.GlobalNaturality

/-! # Shifted Hom Iso Normalization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ShiftedHomIsoNormalization

noncomputable section

/-! # Transporting a small derived morphism by two genuine complex isomorphisms -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

local notation "QI" => HomologicalComplex.quasiIso C ℤᵘᵖ

theorem smallShiftedHomIso_normalization {A B A' B' : CochainComplex C ℤ}
    [Localization.HasSmallLocalizedShiftedHom.{w} (QI) ℤ A A]
    [Localization.HasSmallLocalizedShiftedHom.{w} (QI) ℤ A' A']
    [Localization.HasSmallLocalizedShiftedHom.{w} (QI) ℤ A A']
    [Localization.HasSmallLocalizedShiftedHom.{w} (QI) ℤ A' A]
    [Localization.HasSmallLocalizedShiftedHom.{w} (QI) ℤ A' B]
    [Localization.HasSmallLocalizedShiftedHom.{w} (QI) ℤ A B]
    [Localization.HasSmallLocalizedShiftedHom.{w} (QI) ℤ B B]
    [Localization.HasSmallLocalizedShiftedHom.{w} (QI) ℤ B B']
    [Localization.HasSmallLocalizedShiftedHom.{w} (QI) ℤ A' B']
    [Localization.HasSmallLocalizedShiftedHom.{w} (QI) ℤ B' B']
    (eA : A ≅ A') (eB : B ≅ B') (n : ℤ)
    (a : Localization.SmallShiftedHom.{w} (QI) A B n) :
    Localization.SmallShiftedHom.equiv (QI) DerivedCategory.Q
      (((Localization.SmallShiftedHom.precompEquiv eA.hom
          ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)).symm a).comp
        (Localization.SmallShiftedHom.mk₀ (QI) (0 : ℤ) rfl eB.hom) (zero_add n)) =
      DerivedCategory.Q.map eA.inv ≫
        Localization.SmallShiftedHom.equiv (QI) DerivedCategory.Q a ≫
          (DerivedCategory.Q.map eB.hom)⟦n⟧' := by
  have hi : (Localization.isoOfHom DerivedCategory.Q (QI) eA.hom
      ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)).inv =
      DerivedCategory.Q.map eA.inv := by
    apply (cancel_mono (DerivedCategory.Q.map eA.hom)).1
    rw [Localization.isoOfHom_inv_hom_id, ← CategoryTheory.Functor.map_comp, eA.inv_hom_id]
    exact (CategoryTheory.Functor.map_id DerivedCategory.Q _).symm
  change Localization.SmallShiftedHom.equiv (QI) DerivedCategory.Q
    (((Localization.SmallShiftedHom.mk₀Inv (W := (QI)) (0 : ℤ) rfl eA.hom
        ((HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance)).comp a (add_zero n)).comp
      (Localization.SmallShiftedHom.mk₀ (QI) (0 : ℤ) rfl eB.hom) (zero_add n)) = _
  rw [Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_comp,
    Localization.SmallShiftedHom.equiv_mk₀Inv, Localization.SmallShiftedHom.equiv_mk₀]
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, hi]
  exact Category.assoc _ _ _

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ShiftedHomIsoNormalization
