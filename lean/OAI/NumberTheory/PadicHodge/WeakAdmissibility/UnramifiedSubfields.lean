import OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientFunctoriality
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.ResidueCoefficientField

/-! # Unramified Subfields -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.UnramifiedSubfields

noncomputable section

/-! Unramified subextensions defined by their actual finite etale integer rings. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteFieldResidue OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientFunctoriality.ValuationRing OAI.NumberTheory.PadicHodge.WeakAdmissibility.ResidueCoefficientField
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.UnramifiedCoefficients OAI.NumberTheory.PadicHodge.WeakAdmissibility.AlgebraicCoefficientFields
variable (p : ℕ) [Fact p.Prime]
variable (L : IntermediateField ℚ_[p] (PadicAlgCl p))

instance integerBaseFieldAlgebra : Algebra ℤ_[p] L :=
  ((algebraMap ℚ_[p] L).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

instance integerBaseFieldModule : Module ℤ_[p] L := Algebra.toModule

instance integerBasePadicTower : IsScalarTower ℤ_[p] ℚ_[p] L :=
  IsScalarTower.of_algebraMap_eq (R := ℤ_[p]) (S := ℚ_[p]) (A := L) fun _ => rfl

instance integerBaseValuationTower : IsScalarTower ℤ_[p] (FiniteFieldResidue.FieldIntegers p L) L :=
  IsScalarTower.of_algebraMap_eq (R := ℤ_[p]) (S := FiniteFieldResidue.FieldIntegers p L) (A := L) fun _ => rfl

theorem padicToFieldIntegers_injective : Function.Injective (CoefficientFunctoriality.ValuationRing.padicToFieldIntegers p L) := by
  intro a b hab
  have h := congrArg Subtype.val hab
  change algebraMap ℚ_[p] L (a : ℚ_[p]) = algebraMap ℚ_[p] L (b : ℚ_[p]) at h
  exact Subtype.ext ((algebraMap ℚ_[p] L).injective h)

instance fieldIntegersTorsionFree : Module.IsTorsionFree ℤ_[p] (FiniteFieldResidue.FieldIntegers p L) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (padicToFieldIntegers_injective p L)

/-- A finite unramified extension has a finite etale actual valuation ring over Z_p. -/
def IsUnramified : Prop :=
  Module.Finite ℤ_[p] (FiniteFieldResidue.FieldIntegers p L) ∧ Algebra.Etale ℤ_[p] (FiniteFieldResidue.FieldIntegers p L)

variable [Module.Finite ℚ_[p] L]

theorem unramified_finrank (hL : IsUnramified p L) :
    Module.finrank ℚ_[p] L = (UnramifiedCoefficients.residueDegree (p := p) (k := FiniteFieldResidue.FieldResidue p L) : ℕ) := by
  let : Module.Finite ℤ_[p] (FiniteFieldResidue.FieldIntegers p L) := hL.1
  let : Algebra.Etale ℤ_[p] (FiniteFieldResidue.FieldIntegers p L) := hL.2
  rw [IsFractionRing.finrank_eq ℤ_[p] ℚ_[p] (FiniteFieldResidue.FieldIntegers p L) L,
    IsLocalRing.finrank_eq_finrank_residueField]
  apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
  have he := Module.natCard_eq_pow_finrank (K := IsLocalRing.ResidueField ℤ_[p])
    (V := FiniteFieldResidue.FieldResidue p L)
  have hbase : Nat.card (IsLocalRing.ResidueField ℤ_[p]) = p := by
    rw [Nat.card_congr (PadicInt.residueField (p := p)).toEquiv, Nat.card_eq_fintype_card, ZMod.card]
  rw [hbase, Nat.card_eq_fintype_card, UnramifiedCoefficients.residueDegree_card] at he
  exact he.symm

theorem unramified_eq_residueCoefficient (hL : IsUnramified p L) :
    ResidueCoefficientField.residueCoefficientSubfield p L = L := by
  apply IntermediateField.eq_of_le_of_finrank_eq (ResidueCoefficientField.residueCoefficientSubfield_le p L)
  change Module.finrank ℚ_[p] (AlgebraicCoefficientFields.coefficientSubfield p (FiniteFieldResidue.residueEmbedding p L)) = Module.finrank ℚ_[p] L
  rw [← (AlgebraicCoefficientFields.coefficientSubfieldEquiv p (FiniteFieldResidue.residueEmbedding p L)).toLinearEquiv.finrank_eq,
    ResidueCoefficientField.residueCoefficient_finrank, unramified_finrank p L hL]

theorem residueCoefficient_isUnramified : IsUnramified p (ResidueCoefficientField.residueCoefficientSubfield p L) :=
  ⟨CoefficientFunctoriality.ValuationRing.coefficientIntegersFinite p (FiniteFieldResidue.residueEmbedding p L), CoefficientFunctoriality.ValuationRing.coefficientIntegersEtale p (FiniteFieldResidue.residueEmbedding p L)⟩

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.UnramifiedSubfields
