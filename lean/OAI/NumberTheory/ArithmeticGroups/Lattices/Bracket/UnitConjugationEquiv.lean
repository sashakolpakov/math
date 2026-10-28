import OAI.NumberTheory.ArithmeticGroups.Lattices.VolumeBracketActionOrbit

/-! # Unit Conjugation Equiv -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitConjugationEquiv.Construction

noncomputable section

/-! Conjugating the bracket gives a topological group equivalence
between its full automorphism groups. -/

open scoped OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitAction.Construction.BracketAction

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]

theorem bracket_unit_conjugation_mem (B : L →L[ℝ] L →L[ℝ] L) (a : (L →L[ℝ] L)ˣ)
    (g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) : a * g.val * a⁻¹ ∈ UnipotentBracketGroup.Construction.continuousBracketUnitGroup (a • B) := by
  apply (VolumeBracketActionOrbit.Construction.bracket_unit_smul_eq_iff (a • B) _).mp
  have hg := (VolumeBracketActionOrbit.Construction.bracket_unit_smul_eq_iff B g.val).mpr g.property
  simp only [mul_smul, inv_smul_smul, hg]

theorem bracket_unit_conjugation_back_mem (B : L →L[ℝ] L →L[ℝ] L) (a : (L →L[ℝ] L)ˣ)
    (g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup (a • B)) : a⁻¹ * g.val * a ∈ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B := by
  apply (VolumeBracketActionOrbit.Construction.bracket_unit_smul_eq_iff B _).mp
  have hg := (VolumeBracketActionOrbit.Construction.bracket_unit_smul_eq_iff (a • B) g.val).mpr g.property
  simp only [mul_smul, hg, inv_smul_smul]

def bracketUnitConjugationHom (B : L →L[ℝ] L →L[ℝ] L) (a : (L →L[ℝ] L)ˣ) :
    UnipotentBracketGroup.Construction.continuousBracketUnitGroup B →* UnipotentBracketGroup.Construction.continuousBracketUnitGroup (a • B) where
  toFun g := ⟨a * g.val * a⁻¹, bracket_unit_conjugation_mem B a g⟩
  map_one' := by apply Subtype.ext; change a * 1 * a⁻¹ = 1; group
  map_mul' g h := by
    apply Subtype.ext
    change a * (g.val * h.val) * a⁻¹ = (a * g.val * a⁻¹) * (a * h.val * a⁻¹)
    group

def bracketUnitConjugationBackHom (B : L →L[ℝ] L →L[ℝ] L) (a : (L →L[ℝ] L)ˣ) :
    UnipotentBracketGroup.Construction.continuousBracketUnitGroup (a • B) →* UnipotentBracketGroup.Construction.continuousBracketUnitGroup B where
  toFun g := ⟨a⁻¹ * g.val * a, bracket_unit_conjugation_back_mem B a g⟩
  map_one' := by apply Subtype.ext; change a⁻¹ * 1 * a = 1; group
  map_mul' g h := by
    apply Subtype.ext
    change a⁻¹ * (g.val * h.val) * a = (a⁻¹ * g.val * a) * (a⁻¹ * h.val * a)
    group

def bracketUnitConjugationEquiv (B : L →L[ℝ] L →L[ℝ] L) (a : (L →L[ℝ] L)ˣ) :
    UnipotentBracketGroup.Construction.continuousBracketUnitGroup B ≃ₜ* UnipotentBracketGroup.Construction.continuousBracketUnitGroup (a • B) where
  toFun := bracketUnitConjugationHom B a
  invFun := bracketUnitConjugationBackHom B a
  left_inv g := by
    apply Subtype.ext
    change a⁻¹ * (a * g.val * a⁻¹) * a = g.val
    group
  right_inv g := by
    apply Subtype.ext
    change a * (a⁻¹ * g.val * a) * a⁻¹ = g.val
    group
  map_mul' := (bracketUnitConjugationHom B a).map_mul
  continuous_toFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitConjugationEquiv.Construction
