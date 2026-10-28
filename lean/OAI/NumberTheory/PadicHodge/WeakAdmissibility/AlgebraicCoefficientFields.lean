import OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientComparison

/-! # Algebraic Coefficient Fields -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.AlgebraicCoefficientFields

noncomputable section

/-! The finite Witt coefficient fields as actual subfields of the fixed algebraic closure. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.UnramifiedCoefficients OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientFiniteness OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientComparison
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.PrimitiveElements OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField.Constants OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamDVR
variable (p : ℕ) [Fact p.Prime]

theorem integralComplex_mem_algebraicRange (a : ℂ_[p]) (ha : IsIntegral ℚ_[p] a) :
    ∃ b : PadicAlgCl p, algebraMap (PadicAlgCl p) ℂ_[p] b = a := by
  have ha' : IsIntegral (PadicAlgCl p) a := ha.tower_top
  let P := minpoly (PadicAlgCl p) a
  have hd : P.degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible (PadicAlgCl p) (minpoly.irreducible ha')
  have hm : P.leadingCoeff = 1 := (minpoly.monic ha').leadingCoeff
  have hr : Polynomial.aeval a P = 0 := minpoly.aeval (PadicAlgCl p) a
  rw [Polynomial.eq_X_add_C_of_degree_eq_one hd, hm, Polynomial.C_1, one_mul,
    Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C, add_eq_zero_iff_eq_neg] at hr
  exact ⟨-P.coeff 0, (map_neg (algebraMap (PadicAlgCl p) ℂ_[p]) _).trans hr.symm⟩

variable {k : Type*} [Field k] [Fintype k] [CharP k p] (j : k →+* PrimitiveElements.ResidueCp p)

def coefficientResidueAlg : UnramifiedCoefficients.CoefficientField (p := p) (k := k) →ₐ[ℚ_[p]] ℂ_[p] :=
  (DeRhamField.Constants.residueAlg p).comp (CoefficientComparison.coefficientFieldToCompletionAlg p j)

theorem coefficientResidue_integral (x : UnramifiedCoefficients.CoefficientField (p := p) (k := k)) :
    IsIntegral ℚ_[p] (coefficientResidueAlg p j x) :=
  (Algebra.IsIntegral.isIntegral x).map (coefficientResidueAlg p j)

def coefficientAlgebraicLift (x : UnramifiedCoefficients.CoefficientField (p := p) (k := k)) : PadicAlgCl p :=
  (integralComplex_mem_algebraicRange p _ (coefficientResidue_integral p j x)).choose

theorem coefficientAlgebraicLift_spec (x : UnramifiedCoefficients.CoefficientField (p := p) (k := k)) :
    algebraMap (PadicAlgCl p) ℂ_[p] (coefficientAlgebraicLift p j x) = coefficientResidueAlg p j x :=
  (integralComplex_mem_algebraicRange p _ (coefficientResidue_integral p j x)).choose_spec

def coefficientFieldToAlgebraic : UnramifiedCoefficients.CoefficientField (p := p) (k := k) →ₐ[ℚ_[p]] PadicAlgCl p where
  toFun := coefficientAlgebraicLift p j
  map_zero' := by
    apply (algebraMap (PadicAlgCl p) ℂ_[p]).injective
    rw [coefficientAlgebraicLift_spec, map_zero, map_zero]
  map_one' := by
    apply (algebraMap (PadicAlgCl p) ℂ_[p]).injective
    rw [coefficientAlgebraicLift_spec, map_one, map_one]
  map_add' x y := by
    apply (algebraMap (PadicAlgCl p) ℂ_[p]).injective
    rw [coefficientAlgebraicLift_spec, map_add, map_add,
      coefficientAlgebraicLift_spec, coefficientAlgebraicLift_spec]
  map_mul' x y := by
    apply (algebraMap (PadicAlgCl p) ℂ_[p]).injective
    rw [coefficientAlgebraicLift_spec, map_mul, map_mul,
      coefficientAlgebraicLift_spec, coefficientAlgebraicLift_spec]
  commutes' a := by
    apply (algebraMap (PadicAlgCl p) ℂ_[p]).injective
    rw [coefficientAlgebraicLift_spec, (coefficientResidueAlg p j).commutes,
      ← IsScalarTower.algebraMap_apply]

theorem coefficientFieldToAlgebraic_residue (x : UnramifiedCoefficients.CoefficientField (p := p) (k := k)) :
    algebraMap (PadicAlgCl p) ℂ_[p] (coefficientFieldToAlgebraic p j x) = coefficientResidueAlg p j x :=
  coefficientAlgebraicLift_spec p j x

theorem coefficientFieldToAlgebraic_completion (x : UnramifiedCoefficients.CoefficientField (p := p) (k := k)) :
    DeRhamField.Constants.algebraicToBdRPlus p (coefficientFieldToAlgebraic p j x) = CoefficientComparison.coefficientFieldToCompletion p j x := by
  apply DeRhamField.Constants.integral_residue_injective p
    (DeRhamField.Constants.algebraicLift_integral p (coefficientFieldToAlgebraic p j x))
    (CoefficientComparison.coefficientFieldToCompletion_integral p j x)
  change DeRhamDVR.residue p (DeRhamField.Constants.algebraicToBdRPlus p (coefficientFieldToAlgebraic p j x)) = _
  rw [DeRhamField.Constants.algebraicToBdRPlus_residue, coefficientFieldToAlgebraic_residue]
  rfl

def coefficientSubfield : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  (coefficientFieldToAlgebraic p j).fieldRange

def coefficientSubfieldEquiv : UnramifiedCoefficients.CoefficientField (p := p) (k := k) ≃ₐ[ℚ_[p]] coefficientSubfield p j :=
  (coefficientFieldToAlgebraic p j).equivFieldRange

instance coefficientSubfield_finite : Module.Finite ℚ_[p] (coefficientSubfield p j) :=
  Module.Finite.of_surjective (coefficientSubfieldEquiv p j).toLinearMap
    (coefficientSubfieldEquiv p j).surjective

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.AlgebraicCoefficientFields
