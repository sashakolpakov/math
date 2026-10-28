import OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientIntegers
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteFieldResidue

/-! # Coefficient Functoriality -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.WeakAdmissibility.CoefficientFunctoriality.ValuationRing

/-! The actual valuation ring of a coefficient subfield is its finite etale Witt ring. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.PrimitiveElements OAI.NumberTheory.PadicHodge.WeakAdmissibility.UnramifiedCoefficients OAI.NumberTheory.PadicHodge.WeakAdmissibility.AlgebraicCoefficientFields
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientIntegers OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteFieldResidue OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientFiniteness OAI.NumberTheory.PadicHodge.WeakAdmissibility.WittFinite
variable (p : ℕ) [Fact p.Prime]
variable {k : Type*} [Field k] [Fintype k] [CharP k p] (j : k →+* PrimitiveElements.ResidueCp p)

def wittToSubfield : WittVector p k →+* AlgebraicCoefficientFields.coefficientSubfield p j :=
  (AlgebraicCoefficientFields.coefficientSubfieldEquiv p j).toRingHom.comp
    (algebraMap (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)))

theorem wittToSubfield_norm (a : WittVector p k) : ‖wittToSubfield p j a‖ ≤ 1 :=
  (CoefficientIntegers.coefficientAlgebraic_norm_le_iff p j _).mpr ⟨a, rfl⟩

def wittToIntegers : WittVector p k →+* FiniteFieldResidue.FieldIntegers p (AlgebraicCoefficientFields.coefficientSubfield p j) where
  toFun a := ⟨wittToSubfield p j a, wittToSubfield_norm p j a⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' a b := Subtype.ext (map_add _ a b)
  map_mul' a b := Subtype.ext (map_mul _ a b)

theorem wittToIntegers_injective : Function.Injective (wittToIntegers p j) := by
  intro a b h
  apply IsFractionRing.injective (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k))
  apply (AlgebraicCoefficientFields.coefficientSubfieldEquiv p j).injective
  exact congrArg Subtype.val h

theorem wittToIntegers_surjective : Function.Surjective (wittToIntegers p j) := by
  intro y
  obtain ⟨x, hx⟩ := (AlgebraicCoefficientFields.coefficientSubfieldEquiv p j).surjective y.val
  have hn : ‖AlgebraicCoefficientFields.coefficientFieldToAlgebraic p j x‖ ≤ 1 := by
    have h := y.property
    change ‖y.val‖ ≤ 1 at h
    rw [← hx] at h
    exact h
  obtain ⟨a, ha⟩ := (CoefficientIntegers.coefficientAlgebraic_norm_le_iff p j x).mp hn
  refine ⟨a, Subtype.ext ?_⟩
  change AlgebraicCoefficientFields.coefficientSubfieldEquiv p j
    (algebraMap (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) a) = y.val
  rw [ha, hx]

def wittIntegersEquiv : WittVector p k ≃+* FiniteFieldResidue.FieldIntegers p (AlgebraicCoefficientFields.coefficientSubfield p j) :=
  RingEquiv.ofBijective (wittToIntegers p j) ⟨wittToIntegers_injective p j, wittToIntegers_surjective p j⟩

def padicToFieldIntegers (L : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    ℤ_[p] →+* FiniteFieldResidue.FieldIntegers p L where
  toFun a := ⟨algebraMap ℚ_[p] L (a : ℚ_[p]), by
    change ‖algebraMap ℚ_[p] L (a : ℚ_[p])‖ ≤ 1
    rw [norm_algebraMap']
    exact a.property⟩
  map_zero' := Subtype.ext (by simp)
  map_one' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

instance fieldIntegersPadicAlgebra (L : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    Algebra ℤ_[p] (FiniteFieldResidue.FieldIntegers p L) := (padicToFieldIntegers p L).toAlgebra

theorem wittToIntegers_padic (a : ℤ_[p]) :
    wittToIntegers p j (WittFinite.padicToWitt p k a) = padicToFieldIntegers p (AlgebraicCoefficientFields.coefficientSubfield p j) a := by
  apply Subtype.ext
  change AlgebraicCoefficientFields.coefficientSubfieldEquiv p j (CoefficientFiniteness.padicIntegerToCoefficient p k a) =
    algebraMap ℚ_[p] (AlgebraicCoefficientFields.coefficientSubfield p j) (algebraMap ℤ_[p] ℚ_[p] a)
  rw [← CoefficientFiniteness.padicToCoefficient_integer]
  exact (AlgebraicCoefficientFields.coefficientSubfieldEquiv p j).commutes _

def wittIntegersAlgEquiv : WittVector p k ≃ₐ[ℤ_[p]] FiniteFieldResidue.FieldIntegers p (AlgebraicCoefficientFields.coefficientSubfield p j) :=
  { wittIntegersEquiv p j with commutes' := wittToIntegers_padic p j }

instance coefficientIntegersFinite : Module.Finite ℤ_[p] (FiniteFieldResidue.FieldIntegers p (AlgebraicCoefficientFields.coefficientSubfield p j)) :=
  Module.Finite.of_surjective (wittIntegersAlgEquiv p j).toLinearMap (wittIntegersAlgEquiv p j).surjective

instance coefficientIntegersEtale : Algebra.Etale ℤ_[p] (FiniteFieldResidue.FieldIntegers p (AlgebraicCoefficientFields.coefficientSubfield p j)) :=
  Algebra.Etale.of_equiv (wittIntegersAlgEquiv p j)

end NumberTheory.PadicHodge.WeakAdmissibility.CoefficientFunctoriality.ValuationRing

namespace NumberTheory.PadicHodge.WeakAdmissibility.CoefficientFunctoriality

/-! Functoriality of the actual coefficient subfields under finite residue-field inclusions. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.PrimitiveElements OAI.NumberTheory.PadicHodge.WeakAdmissibility.TiltCoefficients OAI.NumberTheory.PadicHodge.WeakAdmissibility.UnramifiedCoefficients
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.AlgebraicCoefficientFields OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientComparison OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField.Constants OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEmbedding
variable (p : ℕ) [Fact p.Prime]
variable {k l : Type*} [Field k] [Fintype k] [CharP k p] [Field l] [Fintype l] [CharP l p]
variable (i : k →+* l) (j : l →+* PrimitiveElements.ResidueCp p)

theorem coefficientEmbedding_comp (a : k) :
    TiltCoefficients.coefficientEmbedding p j (i a) = TiltCoefficients.coefficientEmbedding p (j.comp i) a := by
  apply TiltCoefficients.integral_tilt_residue_injective p (TiltCoefficients.coefficientLift_integral p j (i a))
    (TiltCoefficients.coefficientLift_integral p (j.comp i) a)
  rw [TiltCoefficients.coefficientLift_residue, TiltCoefficients.coefficientLift_residue]
  rfl

theorem coefficientToAInf_comp (x : WittVector p k) :
    UnramifiedCoefficients.coefficientToAInf p j (WittVector.map i x) = UnramifiedCoefficients.coefficientToAInf p (j.comp i) x := by
  change WittVector.map (TiltCoefficients.coefficientEmbedding p j) (WittVector.map i x) =
    WittVector.map (TiltCoefficients.coefficientEmbedding p (j.comp i)) x
  ext n
  simp only [WittVector.map_coeff, coefficientEmbedding_comp]

theorem coefficientToCompletion_comp (x : WittVector p k) :
    CoefficientComparison.coefficientToCompletion p j (WittVector.map i x) = CoefficientComparison.coefficientToCompletion p (j.comp i) x :=
  congrArg (DeRhamEmbedding.aInfToBdRPlus p) (coefficientToAInf_comp p i j x)

theorem coefficientAlgebraic_integer_comp (x : WittVector p k) :
    AlgebraicCoefficientFields.coefficientFieldToAlgebraic p j
      (algebraMap (WittVector p l) (UnramifiedCoefficients.CoefficientField (p := p) (k := l)) (WittVector.map i x)) =
        AlgebraicCoefficientFields.coefficientFieldToAlgebraic p (j.comp i)
          (algebraMap (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) x) := by
  apply (DeRhamField.Constants.algebraicToBdRPlus p).injective
  change DeRhamField.Constants.algebraicToBdRPlus p (AlgebraicCoefficientFields.coefficientFieldToAlgebraic p j
    (algebraMap (WittVector p l) (UnramifiedCoefficients.CoefficientField (p := p) (k := l)) (WittVector.map i x))) =
      DeRhamField.Constants.algebraicToBdRPlus p (AlgebraicCoefficientFields.coefficientFieldToAlgebraic p (j.comp i)
        (algebraMap (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) x))
  rw [AlgebraicCoefficientFields.coefficientFieldToAlgebraic_completion, AlgebraicCoefficientFields.coefficientFieldToAlgebraic_completion,
    CoefficientComparison.coefficientFieldToCompletion_integer, CoefficientComparison.coefficientFieldToCompletion_integer, coefficientToCompletion_comp]

theorem coefficientSubfield_comp_le : AlgebraicCoefficientFields.coefficientSubfield p (j.comp i) ≤ AlgebraicCoefficientFields.coefficientSubfield p j := by
  intro z hz
  obtain ⟨x, rfl⟩ := AlgHom.mem_fieldRange.mp hz
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := WittVector p k) x
  rw [map_div₀]
  apply IntermediateField.div_mem
  · exact AlgHom.mem_fieldRange.mpr
      ⟨algebraMap (WittVector p l) (UnramifiedCoefficients.CoefficientField (p := p) (k := l)) (WittVector.map i a),
        coefficientAlgebraic_integer_comp p i j a⟩
  · exact AlgHom.mem_fieldRange.mpr
      ⟨algebraMap (WittVector p l) (UnramifiedCoefficients.CoefficientField (p := p) (k := l)) (WittVector.map i b),
        coefficientAlgebraic_integer_comp p i j b⟩

end NumberTheory.PadicHodge.WeakAdmissibility.CoefficientFunctoriality

end

end OAI
