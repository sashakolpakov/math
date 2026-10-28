import OAI.NumberTheory.ArithmeticGroups.Lattices.VolumePreservingOperatorUnits
import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousFrameOperator

/-! # Unit Action -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitAction.Construction.BracketAction

noncomputable section

/-! The change-of-basis action of continuous operator units on
bilinear operations, in a separate scope from ordinary module actions. -/

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

local instance actionEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance actionEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance actionBilinear_normed : NormedAddCommGroup (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance actionBilinear_space : NormedSpace ℝ (L →L[ℝ] L →L[ℝ] L) := inferInstance

scoped instance (priority := 2000) bracketSMul : SMul (L →L[ℝ] L)ˣ (L →L[ℝ] L →L[ℝ] L) where
  smul g B := ContinuousBracketChange.Construction.continuousBracketChange (ContinuousLinearEquiv.ofUnit g) B

open scoped OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitAction.Construction.BracketAction

scoped instance bracketMulAction : MulAction (L →L[ℝ] L)ˣ (L →L[ℝ] L →L[ℝ] L) where
  one_smul B := by ext x y; rfl
  mul_smul g h B := by ext x y; rfl

scoped instance : ContinuousSMul (L →L[ℝ] L)ˣ (L →L[ℝ] L →L[ℝ] L) := by
  constructor
  apply continuous_clm_apply.mpr
  intro x
  apply continuous_clm_apply.mpr
  intro y
  change Continuous (fun z : (L →L[ℝ] L)ˣ × (L →L[ℝ] L →L[ℝ] L) =>
    z.1.val (z.2 ((z.1⁻¹).val x) ((z.1⁻¹).val y)))
  exact (Units.continuous_val.comp continuous_fst).clm_apply
    ((continuous_snd.clm_apply
      ((Units.continuous_val.comp (continuous_inv.comp continuous_fst)).clm_apply continuous_const)).clm_apply
      ((Units.continuous_val.comp (continuous_inv.comp continuous_fst)).clm_apply continuous_const))

scoped instance (priority := 2000) volumeBracketSMul :
    SMul (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) (L →L[ℝ] L →L[ℝ] L) where
  smul g B := g.val • B

scoped instance volumeBracketMulAction :
    MulAction (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) (L →L[ℝ] L →L[ℝ] L) where
  one_smul B := one_smul (M := (L →L[ℝ] L)ˣ) B
  mul_smul g h B := mul_smul g.val h.val B

scoped instance : ContinuousSMul (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L))
    (L →L[ℝ] L →L[ℝ] L) := by
  constructor
  exact (continuous_subtype_val.comp continuous_fst).smul continuous_snd

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitAction.Construction.BracketAction
