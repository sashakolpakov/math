import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.CycleCoordinates
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # Extended Cycle Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ExtendedCycleCoordinates

noncomputable section

/-! Extension by zero preserves actual positive-degree cycle representatives. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
variable (K : CochainComplex AddCommGrpCat.{u} ℕ) (n : ℕ)
  (x : K.X (n + 1)) (hx : K.d (n + 1) (n + 2) x = 0)

include hx in
theorem extendedCycle_closed :
    (K.extend ComplexShape.embeddingUpNat).d ((n + 1 : ℕ) : ℤ) (((n + 1 : ℕ) : ℤ) + 1)
      ((K.extendXIso ComplexShape.embeddingUpNat (i := n + 1) (ComplexShape.embeddingUpNat_f (n + 1))).inv x) = 0 := by
  rw [K.extend_d_eq ComplexShape.embeddingUpNat (i := n + 1) (j := n + 2) (ComplexShape.embeddingUpNat_f (n + 1))
    (by simp only [ComplexShape.embeddingUpNat_f]; omega)]
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply, hx, map_zero]

theorem extendedCycles_coordinates :
    (K.extendCyclesIso ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f (n + 1) =
      ((n + 1 : ℕ) : ℤ) from rfl)).hom
      (Abelian.CycleCoordinates.abelianIntegerCycles (K.extend ComplexShape.embeddingUpNat) ((n + 1 : ℕ) : ℤ)
        ((K.extendXIso ComplexShape.embeddingUpNat (i := n + 1) (ComplexShape.embeddingUpNat_f (n + 1))).inv x)
          (extendedCycle_closed K n x hx)) = SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n K x hx := by
  apply (AddCommGrpCat.mono_iff_injective (K.iCycles (n + 1))).mp inferInstance
  have h := ConcreteCategory.congr_hom
    (K.extendCyclesIso_hom_iCycles ComplexShape.embeddingUpNat (j := n + 1) (ComplexShape.embeddingUpNat_f (n + 1)))
      (Abelian.CycleCoordinates.abelianIntegerCycles (K.extend ComplexShape.embeddingUpNat) ((n + 1 : ℕ) : ℤ)
        ((K.extendXIso ComplexShape.embeddingUpNat (i := n + 1) (ComplexShape.embeddingUpNat_f (n + 1))).inv x)
          (extendedCycle_closed K n x hx))
  simpa only [ConcreteCategory.comp_apply, Abelian.CycleCoordinates.abelianIntegerCycles_i, Iso.inv_hom_id_apply,
    SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk] using h

theorem extendedCycleClass_coordinates :
    (K.extendHomologyIso ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f (n + 1) =
      ((n + 1 : ℕ) : ℤ) from rfl)).hom
      (Abelian.CycleCoordinates.abelianIntegerCycleClass (K.extend ComplexShape.embeddingUpNat) ((n + 1 : ℕ) : ℤ)
        ((K.extendXIso ComplexShape.embeddingUpNat (i := n + 1) (ComplexShape.embeddingUpNat_f (n + 1))).inv x)
          (extendedCycle_closed K n x hx)) = K.homologyπ (n + 1) (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n K x hx) := by
  have h := ConcreteCategory.congr_hom
    (K.homologyπ_extendHomologyIso_hom ComplexShape.embeddingUpNat (j := n + 1) (ComplexShape.embeddingUpNat_f (n + 1)))
      (Abelian.CycleCoordinates.abelianIntegerCycles (K.extend ComplexShape.embeddingUpNat) ((n + 1 : ℕ) : ℤ)
        ((K.extendXIso ComplexShape.embeddingUpNat (i := n + 1) (ComplexShape.embeddingUpNat_f (n + 1))).inv x)
          (extendedCycle_closed K n x hx))
  simp only [ConcreteCategory.comp_apply] at h
  exact h.trans (congrArg (K.homologyπ (n + 1)) (extendedCycles_coordinates K n x hx))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ExtendedCycleCoordinates
