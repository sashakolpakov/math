import OAI.NumberTheory.PadicHodge.WeakAdmissibility.UnramifiedSubfields
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientFunctoriality

/-! # Maximal Unramified -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.MaximalUnramified

noncomputable section

/-! Construction of the actual maximal unramified subextension of K/Q_p. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteFieldResidue OAI.NumberTheory.PadicHodge.WeakAdmissibility.ResidueCoefficientField OAI.NumberTheory.PadicHodge.WeakAdmissibility.UnramifiedSubfields
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientFunctoriality OAI.NumberTheory.PadicHodge.WeakAdmissibility.AlgebraicCoefficientFields OAI.NumberTheory.PadicHodge.WeakAdmissibility.UnramifiedCoefficients
variable (p : ℕ) [Fact p.Prime]
variable {L K : IntermediateField ℚ_[p] (PadicAlgCl p)} (hLK : L ≤ K)

def integerInclusion : FiniteFieldResidue.FieldIntegers p L →+* FiniteFieldResidue.FieldIntegers p K where
  toFun a := ⟨IntermediateField.inclusion hLK a.val, a.property⟩
  map_zero' := Subtype.ext (map_zero (IntermediateField.inclusion hLK))
  map_one' := Subtype.ext (map_one (IntermediateField.inclusion hLK))
  map_add' a b := Subtype.ext (map_add (IntermediateField.inclusion hLK) a.val b.val)
  map_mul' a b := Subtype.ext (map_mul (IntermediateField.inclusion hLK) a.val b.val)

instance integerInclusion_local : IsLocalHom (integerInclusion p hLK) := by
  apply ((IsLocalRing.local_hom_TFAE (integerInclusion p hLK)).out 4 1 rfl rfl).mp
  intro a ha
  change integerInclusion p hLK a ∈ IsLocalRing.maximalIdeal (FiniteFieldResidue.FieldIntegers p K)
  erw [Valuation.mem_maximalIdeal_iff] at ha ⊢
  exact ha

def residueInclusion : FiniteFieldResidue.FieldResidue p L →+* FiniteFieldResidue.FieldResidue p K :=
  IsLocalRing.ResidueField.map (integerInclusion p hLK)

theorem residueInclusion_residue (a : FiniteFieldResidue.FieldIntegers p L) :
    residueInclusion p hLK (IsLocalRing.residue (FiniteFieldResidue.FieldIntegers p L) a) =
      IsLocalRing.residue (FiniteFieldResidue.FieldIntegers p K) (integerInclusion p hLK a) :=
  IsLocalRing.ResidueField.map_residue _ a

theorem residueInclusion_comp :
    (FiniteFieldResidue.residueEmbedding p K).comp (residueInclusion p hLK) = FiniteFieldResidue.residueEmbedding p L := by
  apply RingHom.ext
  intro a
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
  rw [RingHom.comp_apply, residueInclusion_residue, FiniteFieldResidue.residueEmbedding_residue, FiniteFieldResidue.residueEmbedding_residue]
  rfl

include hLK in
theorem residueCoefficient_mono [Module.Finite ℚ_[p] L] [Module.Finite ℚ_[p] K] :
    ResidueCoefficientField.residueCoefficientSubfield p L ≤ ResidueCoefficientField.residueCoefficientSubfield p K := by
  have h := CoefficientFunctoriality.coefficientSubfield_comp_le p (residueInclusion p hLK) (FiniteFieldResidue.residueEmbedding p K)
  rw [residueInclusion_comp] at h
  exact h

include hLK in
theorem unramified_le_coefficient [Module.Finite ℚ_[p] K] (hL : UnramifiedSubfields.IsUnramified p L) :
    L ≤ ResidueCoefficientField.residueCoefficientSubfield p K := by
  let : Module.Finite ℚ_[p] L := Module.Finite.of_injective (IntermediateField.inclusion hLK).toLinearMap
    (IntermediateField.inclusion_injective hLK)
  exact (UnramifiedSubfields.unramified_eq_residueCoefficient p L hL).symm.trans_le (residueCoefficient_mono p hLK)

variable (K) [Module.Finite ℚ_[p] K]

/-- The maximal subextension whose actual integer ring is finite etale over Z_p. -/
def K0 : IntermediateField ℚ_[p] (PadicAlgCl p) := ResidueCoefficientField.residueCoefficientSubfield p K

theorem K0_isGreatest : IsGreatest {L : IntermediateField ℚ_[p] (PadicAlgCl p) |
    L ≤ K ∧ UnramifiedSubfields.IsUnramified p L} (K0 p K) := by
  refine ⟨⟨ResidueCoefficientField.residueCoefficientSubfield_le p K, UnramifiedSubfields.residueCoefficient_isUnramified p K⟩, ?_⟩
  intro L hL
  exact unramified_le_coefficient p hL.1 hL.2

theorem K0_finrank : Module.finrank ℚ_[p] (K0 p K) =
    (UnramifiedCoefficients.residueDegree (p := p) (k := FiniteFieldResidue.FieldResidue p K) : ℕ) := by
  change Module.finrank ℚ_[p] (AlgebraicCoefficientFields.coefficientSubfield p (FiniteFieldResidue.residueEmbedding p K)) = _
  rw [← (AlgebraicCoefficientFields.coefficientSubfieldEquiv p (FiniteFieldResidue.residueEmbedding p K)).toLinearEquiv.finrank_eq]
  exact ResidueCoefficientField.residueCoefficient_finrank p K

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.MaximalUnramified
