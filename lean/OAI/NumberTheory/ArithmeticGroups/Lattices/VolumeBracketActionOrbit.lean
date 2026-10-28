import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitAction
import OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentBracketGroup

/-! # Volume Bracket Action Orbit -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.VolumeBracketActionOrbit.Construction

noncomputable section

/-! The volume-preserving operator action has the previously constructed
closed bracket orbit, and its stabilizer is the bracket automorphism group. -/

open Set MulAction
open scoped OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitAction.Construction.BracketAction

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

omit [FiniteDimensional ℝ L] in
theorem volume_operator_orbit_eq (B : L →L[ℝ] L →L[ℝ] L) :
    orbit (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) B = Bracket.OrbitMinimum.Construction.bracketVolumeOrbit B := by
  ext C
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨ContinuousLinearEquiv.ofUnit g.val, g.property, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨⟨e.toUnit, he⟩, rfl⟩

theorem volume_operator_orbit_isClosed
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) :
    IsClosed (orbit (VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) B) := by
  rw [volume_operator_orbit_eq]
  exact Bracket.OrbitMinimum.Construction.bracketVolumeOrbit_isClosed B hB hK

omit [FiniteDimensional ℝ L] in
theorem bracket_unit_smul_eq_iff (B : L →L[ℝ] L →L[ℝ] L) (g : (L →L[ℝ] L)ˣ) :
    g • B = B ↔ g ∈ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B := by
  constructor
  · intro h x y
    have he := DFunLike.congr_fun (DFunLike.congr_fun h (g.val x)) (g.val y)
    change g.val (B ((g⁻¹).val (g.val x)) ((g⁻¹).val (g.val y))) = _ at he
    simpa only [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def,
      Units.inv_mul, one_apply_eq_self] using he
  · intro h
    ext x y
    change g.val (B ((g⁻¹).val x) ((g⁻¹).val y)) = B x y
    rw [h, UnipotentBracketGroup.Construction.continuousLinearUnit_apply_inv_apply, UnipotentBracketGroup.Construction.continuousLinearUnit_apply_inv_apply]

theorem bracket_unit_volume_preserving
    (B : L →L[ℝ] L →L[ℝ] L) (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (g : (L →L[ℝ] L)ˣ) (hg : g ∈ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) :
    g ∈ VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits := by
  apply Bracket.KillingDeterminant.Construction.abs_det_one_of_bracketKillingDeterminant_eq (Module.finBasis ℝ L)
    (ContinuousLinearEquiv.ofUnit g) B hK
  exact congrArg (Bracket.KillingDeterminant.Construction.bracketKillingDeterminant (Module.finBasis ℝ L) ·)
    ((bracket_unit_smul_eq_iff B g).mpr hg)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.VolumeBracketActionOrbit.Construction
