import OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteFieldResidue
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientGalois

/-! # Residue Coefficient Field -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.ResidueCoefficientField

noncomputable section

/-! The residue coefficient field selected by K and its actual embedding into K. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.PrimitiveElements OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteFieldResidue OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientGalois
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.UnramifiedCoefficients OAI.NumberTheory.PadicHodge.WeakAdmissibility.AlgebraicCoefficientFields OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField.Scalars OAI.NumberTheory.PadicHodge.WeakAdmissibility.Galois
variable (p : ℕ) [Fact p.Prime]
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem integerToCp_fixed (σ : K.fixingSubgroup) (a : FiniteFieldResidue.FieldIntegers p K) :
    PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ.val (FiniteFieldResidue.integerToCp p K a) = FiniteFieldResidue.integerToCp p K a := by
  apply Subtype.ext
  change PeriodInvariants.PeriodRing.galoisComplexEquiv p σ.val
    (algebraMap (PadicAlgCl p) ℂ_[p] (a.val : PadicAlgCl p)) =
      algebraMap (PadicAlgCl p) ℂ_[p] (a.val : PadicAlgCl p)
  rw [DeRhamField.Scalars.galoisComplexEquiv_algebraic]
  exact congrArg (algebraMap (PadicAlgCl p) ℂ_[p]) (σ.property a.val)

theorem residueEmbedding_fixed (σ : K.fixingSubgroup) (a : FiniteFieldResidue.FieldResidue p K) :
    CoefficientGalois.galoisResidue p σ.val (FiniteFieldResidue.residueEmbedding p K a) = FiniteFieldResidue.residueEmbedding p K a := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
  rw [FiniteFieldResidue.residueEmbedding_residue, CoefficientGalois.galoisResidue_residue, integerToCp_fixed]

theorem conjugateResidue_eq (σ : K.fixingSubgroup) :
    CoefficientGalois.conjugateResidue p (FiniteFieldResidue.residueEmbedding p K) σ.val = FiniteFieldResidue.residueEmbedding p K := by
  apply RingHom.ext
  exact residueEmbedding_fixed p K σ

variable [Module.Finite ℚ_[p] K]

abbrev ResidueCoefficient := UnramifiedCoefficients.CoefficientField (p := p) (k := FiniteFieldResidue.FieldResidue p K)

def residueCoefficientSubfield : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  AlgebraicCoefficientFields.coefficientSubfield p (FiniteFieldResidue.residueEmbedding p K)

theorem coefficientAlgebraic_fixed (σ : K.fixingSubgroup) (a : ResidueCoefficient p K) :
    σ.val (AlgebraicCoefficientFields.coefficientFieldToAlgebraic p (FiniteFieldResidue.residueEmbedding p K) a) =
      AlgebraicCoefficientFields.coefficientFieldToAlgebraic p (FiniteFieldResidue.residueEmbedding p K) a := by
  rw [CoefficientGalois.coefficientFieldToAlgebraic_galois, conjugateResidue_eq]

theorem residueCoefficientSubfield_le : residueCoefficientSubfield p K ≤ K := by
  refine le_trans (b := IntermediateField.fixedField K.fixingSubgroup) ?_
    (le_of_eq (InfiniteGalois.fixedField_fixingSubgroup K))
  intro a ha
  obtain ⟨x, rfl⟩ := (AlgHom.mem_fieldRange (f := AlgebraicCoefficientFields.coefficientFieldToAlgebraic p (FiniteFieldResidue.residueEmbedding p K))).mp ha
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  exact coefficientAlgebraic_fixed p K ⟨σ, hσ⟩ x

def coefficientToK : ResidueCoefficient p K →ₐ[ℚ_[p]] K where
  toFun a := ⟨AlgebraicCoefficientFields.coefficientFieldToAlgebraic p (FiniteFieldResidue.residueEmbedding p K) a,
    residueCoefficientSubfield_le p K (AlgHom.mem_fieldRange.mpr ⟨a, rfl⟩)⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' a b := Subtype.ext (map_add _ a b)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  commutes' a := Subtype.ext ((AlgebraicCoefficientFields.coefficientFieldToAlgebraic p (FiniteFieldResidue.residueEmbedding p K)).commutes a)

theorem coefficientBCris_fixed (σ : K.fixingSubgroup) (a : ResidueCoefficient p K) :
    Galois.galoisBCrisMap p σ.val (UnramifiedCoefficients.coefficientFieldToBCris p (FiniteFieldResidue.residueEmbedding p K) a) =
      UnramifiedCoefficients.coefficientFieldToBCris p (FiniteFieldResidue.residueEmbedding p K) a := by
  rw [CoefficientGalois.coefficientFieldToBCris_galois, conjugateResidue_eq]

theorem residueCoefficient_finrank :
    Module.finrank ℚ_[p] (ResidueCoefficient p K) =
      (UnramifiedCoefficients.residueDegree (p := p) (k := FiniteFieldResidue.FieldResidue p K) : ℕ) :=
  WittUnramified.coefficientField_finrank p (FiniteFieldResidue.FieldResidue p K)

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.ResidueCoefficientField
