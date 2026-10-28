import OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.IntegralDiscrete
import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.KernelDiscrete
import OAI.NumberTheory.ArithmeticGroups.Lattices.VolumeBracketActionOrbit

/-! # Conjugation Action -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.ConjugationAction.Construction

noncomputable section

section

/-! The integral subgroup in a conjugated bracket realization is
the discrete pullback of the ambient integral operator group. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def bracketVolumeHom (B : L →L[ℝ] L →L[ℝ] L) (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) :
    UnipotentBracketGroup.Construction.continuousBracketUnitGroup B →* VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L) where
  toFun g := ⟨g.val, VolumeBracketActionOrbit.Construction.bracket_unit_volume_preserving B hK g.val g.property⟩
  map_one' := by apply Subtype.ext; rfl
  map_mul' g h := by apply Subtype.ext; rfl

theorem bracketVolumeHom_continuous (B : L →L[ℝ] L →L[ℝ] L)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) : Continuous (bracketVolumeHom B hK) :=
  continuous_subtype_val.subtype_mk _

theorem bracketVolumeHom_injective (B : L →L[ℝ] L →L[ℝ] L)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) : Function.Injective (bracketVolumeHom B hK) := by
  intro g h he
  have hv : g.val = h.val := congrArg (fun z : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L) => z.val) he
  exact Subtype.ext hv

def conjugatedBracketVolumeHom (B : L →L[ℝ] L →L[ℝ] L)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) (a : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) :
    UnipotentBracketGroup.Construction.continuousBracketUnitGroup B →* VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L) :=
  (MulAut.conj a⁻¹).toMonoidHom.comp (bracketVolumeHom B hK)

theorem conjugatedBracketVolumeHom_continuous (B : L →L[ℝ] L →L[ℝ] L)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) (a : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) :
    Continuous (conjugatedBracketVolumeHom B hK a) :=
  (continuous_const.mul (bracketVolumeHom_continuous B hK)).mul continuous_const

theorem conjugatedBracketVolumeHom_injective (B : L →L[ℝ] L →L[ℝ] L)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) (a : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) :
    Function.Injective (conjugatedBracketVolumeHom B hK a) :=
  (MulAut.conj a⁻¹).injective.comp (bracketVolumeHom_injective B hK)

def conjugatedIntegralBracketSubgroup {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (B : L →L[ℝ] L →L[ℝ] L) (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (a : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) : Subgroup (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) :=
  (VolumeOperatorSiegelCover.Construction.ambientIntegralOperatorGroup b).comap (conjugatedBracketVolumeHom B hK a)

theorem conjugatedIntegralBracketSubgroup_discrete {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (B : L →L[ℝ] L →L[ℝ] L) (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (a : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) : DiscreteTopology (conjugatedIntegralBracketSubgroup b B hK a) := by
  let f := conjugatedBracketVolumeHom B hK a
  let : Subsingleton f.ker := ⟨fun x y => Subtype.ext
    (conjugatedBracketVolumeHom_injective B hK a (x.property.trans y.property.symm))⟩
  let : Finite f.ker := inferInstance
  let : DiscreteTopology (VolumeOperatorSiegelCover.Construction.ambientIntegralOperatorGroup b) := Ambient.IntegralDiscrete.Construction.ambientIntegralOperatorGroup_discrete b
  exact Lattices.Finite.KernelDiscrete.Construction.discrete_comap_of_finite_kernel f (conjugatedBracketVolumeHom_continuous B hK a)
    (VolumeOperatorSiegelCover.Construction.ambientIntegralOperatorGroup b)

end

/-! Bracket stabilizers and the ambient volume action agree under
the conjugation used in the self-adjoint realization. -/

open scoped OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.UnitAction.Construction.BracketAction

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem bracketVolumeHom_smul (B : L →L[ℝ] L →L[ℝ] L)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) (g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) :
    bracketVolumeHom B hK g • B = B := by
  change g.val • B = B
  exact (VolumeBracketActionOrbit.Construction.bracket_unit_smul_eq_iff B g.val).mpr g.property

theorem conjugatedBracketVolumeHom_apply (B : L →L[ℝ] L →L[ℝ] L)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) (a : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L))
    (g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) :
    conjugatedBracketVolumeHom B hK a g = a⁻¹ * bracketVolumeHom B hK g * a := by
  change a⁻¹ * bracketVolumeHom B hK g * (a⁻¹)⁻¹ = _
  rw [inv_inv]

theorem conjugatedBracketVolumeHom_smul (B : L →L[ℝ] L →L[ℝ] L)
    (a : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L))
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm (a • B)).Nondegenerate)
    (g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup (a • B)) :
    conjugatedBracketVolumeHom (a • B) hK a g • B = B := by
  rw [conjugatedBracketVolumeHom_apply]
  simp only [mul_smul, bracketVolumeHom_smul, inv_smul_smul]

omit [FiniteDimensional ℝ L] in
theorem volume_conjugate_bracket_unit (B : L →L[ℝ] L →L[ℝ] L)
    (a δ : VolumePreservingOperatorUnits.Construction.volumePreservingOperatorUnits (L := L)) (hδ : δ • B = B) :
    (a * δ * a⁻¹).val ∈ UnipotentBracketGroup.Construction.continuousBracketUnitGroup (a • B) := by
  apply (VolumeBracketActionOrbit.Construction.bracket_unit_smul_eq_iff (a • B) (a * δ * a⁻¹).val).mp
  change (a * δ * a⁻¹) • (a • B) = a • B
  simp only [mul_smul, inv_smul_smul, hδ]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.ConjugationAction.Construction
