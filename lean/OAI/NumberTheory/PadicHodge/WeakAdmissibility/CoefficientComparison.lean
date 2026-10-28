import OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientFiniteness
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField

/-! # Coefficient Comparison -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientComparison

noncomputable section

/-! Compatibility of finite Witt coefficient fields with the actual period comparison. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.WittFinite OAI.NumberTheory.PadicHodge.WeakAdmissibility.UnramifiedCoefficients OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientFiniteness
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.PrimitiveElements OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField.Constants OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamDVR OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEmbedding
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonScalars OAI.NumberTheory.PadicHodge.WeakAdmissibility.Galois.PeriodStructure OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRham OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonBd
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Cyclotomic OAI.NumberTheory.PadicHodge.WeakAdmissibility.Comparison OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEnvelope
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm
variable (p : ℕ) [Fact p.Prime]
variable {k : Type*} [Field k] [Fintype k] [CharP k p] (j : k →+* PrimitiveElements.ResidueCp p)

theorem coefficientToAInf_padicInteger (a : ℤ_[p]) :
    UnramifiedCoefficients.coefficientToAInf p j (WittFinite.padicToWitt p k a) = Logarithm.PeriodRings.padicIntToAInf p a :=
  DFunLike.congr_fun (DeRhamField.Constants.padicInt_ringHom_unique p
    ((UnramifiedCoefficients.coefficientToAInf p j).comp (WittFinite.padicToWitt p k)) (Logarithm.PeriodRings.padicIntToAInf p)) a

theorem coefficientToBCris_padicInteger (a : ℤ_[p]) :
    UnramifiedCoefficients.coefficientToBCris p j (WittFinite.padicToWitt p k a) =
      Galois.PeriodStructure.padicToBCris p (algebraMap ℤ_[p] ℚ_[p] a) := by
  rw [Galois.PeriodStructure.padicToBCris, RingHom.comp_apply, Galois.PeriodStructure.padicToPositive_int]
  change algebraMap (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.BCris p)
    (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p)
      (algebraMap (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p)
        (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) (UnramifiedCoefficients.coefficientToAInf p j (WittFinite.padicToWitt p k a))))) = _
  rw [coefficientToAInf_padicInteger]
  rfl

theorem coefficientFieldToBCris_padic (a : ℚ_[p]) :
    UnramifiedCoefficients.coefficientFieldToBCris p j (CoefficientFiniteness.padicToCoefficient p k a) = Galois.PeriodStructure.padicToBCris p a := by
  have he : (UnramifiedCoefficients.coefficientFieldToBCris p j).comp (CoefficientFiniteness.padicToCoefficient p k) = Galois.PeriodStructure.padicToBCris p := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
    apply RingHom.ext
    intro b
    simp only [RingHom.comp_apply, CoefficientFiniteness.padicToCoefficient_integer]
    change UnramifiedCoefficients.coefficientFieldToBCris p j
      (algebraMap (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) (WittFinite.padicToWitt p k b)) = _
    rw [UnramifiedCoefficients.coefficientFieldToBCris_integer, coefficientToBCris_padicInteger]
  exact DFunLike.congr_fun he a

def coefficientFieldToBCrisAlg : UnramifiedCoefficients.CoefficientField (p := p) (k := k) →ₐ[ℚ_[p]] Logarithm.PeriodRings.BCris p :=
  { UnramifiedCoefficients.coefficientFieldToBCris p j with commutes' := coefficientFieldToBCris_padic p j }

def coefficientToCompletion : WittVector p k →+* DeRhamDVR.DeRhamCompletion p :=
  (DeRhamEmbedding.aInfToBdRPlus p).comp (UnramifiedCoefficients.coefficientToAInf p j)

theorem coefficientToCompletion_padicInteger (a : ℤ_[p]) :
    coefficientToCompletion p j (WittFinite.padicToWitt p k a) =
      algebraMap ℚ_[p] (DeRhamDVR.DeRhamCompletion p) (algebraMap ℤ_[p] ℚ_[p] a) := by
  change DeRhamEmbedding.aInfToBdRPlus p (UnramifiedCoefficients.coefficientToAInf p j (WittFinite.padicToWitt p k a)) =
    ComparisonScalars.padicToBdRPlus p (algebraMap ℤ_[p] ℚ_[p] a)
  rw [coefficientToAInf_padicInteger, ComparisonScalars.padicToBdRPlus_integer]
  rfl

theorem coefficientToCompletion_nonzero_isUnit (x : WittVector p k) (hx : x ≠ 0) :
    IsUnit (coefficientToCompletion p j x) := by
  obtain ⟨n, u, hu⟩ := WittVector.exists_eq_pow_p_mul' x hx
  rw [hu, map_mul, map_pow, map_natCast]
  apply IsUnit.mul
  · apply IsUnit.pow
    exact (map_natCast (algebraMap ℚ_[p] (DeRhamDVR.DeRhamCompletion p)) p) ▸
      ((isUnit_iff_ne_zero.mpr (NeZero.ne (p : ℚ_[p]))).map (algebraMap ℚ_[p] (DeRhamDVR.DeRhamCompletion p)))
  · exact u.isUnit.map _

def coefficientFieldToCompletion : UnramifiedCoefficients.CoefficientField (p := p) (k := k) →+* DeRhamDVR.DeRhamCompletion p :=
  IsLocalization.lift (g := coefficientToCompletion p j)
    (fun x : nonZeroDivisors (WittVector p k) => coefficientToCompletion_nonzero_isUnit p j x
      (mem_nonZeroDivisors_iff_ne_zero.mp x.property))

theorem coefficientFieldToCompletion_integer (x : WittVector p k) :
    coefficientFieldToCompletion p j
      (algebraMap (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) x) =
        coefficientToCompletion p j x := by
  unfold coefficientFieldToCompletion
  rw [IsLocalization.lift_eq]

theorem coefficientFieldToCompletion_padic (a : ℚ_[p]) :
    coefficientFieldToCompletion p j (CoefficientFiniteness.padicToCoefficient p k a) =
      algebraMap ℚ_[p] (DeRhamDVR.DeRhamCompletion p) a := by
  have he : (coefficientFieldToCompletion p j).comp (CoefficientFiniteness.padicToCoefficient p k) =
      algebraMap ℚ_[p] (DeRhamDVR.DeRhamCompletion p) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
    apply RingHom.ext
    intro b
    simp only [RingHom.comp_apply, CoefficientFiniteness.padicToCoefficient_integer]
    change coefficientFieldToCompletion p j
      (algebraMap (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) (WittFinite.padicToWitt p k b)) = _
    rw [coefficientFieldToCompletion_integer, coefficientToCompletion_padicInteger]
  exact DFunLike.congr_fun he a

def coefficientFieldToCompletionAlg :
    UnramifiedCoefficients.CoefficientField (p := p) (k := k) →ₐ[ℚ_[p]] DeRhamDVR.DeRhamCompletion p :=
  { coefficientFieldToCompletion p j with commutes' := coefficientFieldToCompletion_padic p j }

theorem coefficientFieldToCompletion_integral (x : UnramifiedCoefficients.CoefficientField (p := p) (k := k)) :
    IsIntegral ℚ_[p] (coefficientFieldToCompletion p j x) :=
  (Algebra.IsIntegral.isIntegral x).map (coefficientFieldToCompletionAlg p j)

theorem coefficientToBCris_comparison (x : WittVector p k) :
    ComparisonBd.bCrisToBdR p (UnramifiedCoefficients.coefficientToBCris p j x) = ComparisonBd.bdRPlusToBdR p (coefficientToCompletion p j x) := by
  change ComparisonBd.bCrisToBdR p (algebraMap (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.BCris p) (UnramifiedCoefficients.coefficientToPositive p j x)) = _
  rw [ComparisonBd.bCrisToBdR_algebraMap]
  change ComparisonBd.bdRPlusToBdR p (Comparison.bCrisPlusToBdRPlus p
    (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p) (UnramifiedCoefficients.coefficientToACris p j x))) = _
  rw [Comparison.bCrisPlusToBdRPlus_algebraMap]
  change ComparisonBd.bdRPlusToBdR p (Comparison.aCrisToBdRPlus p
    (algebraMap (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p) (UnramifiedCoefficients.coefficientToUncompleted p j x))) = _
  rw [Comparison.aCrisToBdRPlus_of]
  change ComparisonBd.bdRPlusToBdR p (DeRhamEnvelope.uncompletedToBdRPlus p
    (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) (UnramifiedCoefficients.coefficientToAInf p j x))) = _
  rw [DeRhamEnvelope.uncompletedToBdRPlus_algebraMap]
  rfl

theorem coefficientFieldToBCris_comparison (x : UnramifiedCoefficients.CoefficientField (p := p) (k := k)) :
    ComparisonBd.bCrisToBdR p (UnramifiedCoefficients.coefficientFieldToBCris p j x) =
      ComparisonBd.bdRPlusToBdR p (coefficientFieldToCompletion p j x) := by
  have he : (ComparisonBd.bCrisToBdR p).comp (UnramifiedCoefficients.coefficientFieldToBCris p j) =
      (ComparisonBd.bdRPlusToBdR p).comp (coefficientFieldToCompletion p j) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (WittVector p k))
    apply RingHom.ext
    intro a
    change ComparisonBd.bCrisToBdR p (UnramifiedCoefficients.coefficientFieldToBCris p j
      (algebraMap (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) a)) =
        ComparisonBd.bdRPlusToBdR p (coefficientFieldToCompletion p j
          (algebraMap (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) a))
    rw [UnramifiedCoefficients.coefficientFieldToBCris_integer, coefficientFieldToCompletion_integer]
    exact coefficientToBCris_comparison p j a
  exact DFunLike.congr_fun he x

include j in
theorem coefficientFrobenius_padic (a : ℚ_[p]) :
    UnramifiedCoefficients.coefficientFrobenius (p := p) (k := k) (algebraMap ℚ_[p] (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) a) =
      algebraMap ℚ_[p] (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) a := by
  apply UnramifiedCoefficients.coefficientFieldToBCris_injective p j
  rw [← UnramifiedCoefficients.coefficientFieldToBCris_frobenius]
  change Logarithm.bCrisFrobenius p (UnramifiedCoefficients.coefficientFieldToBCris p j (CoefficientFiniteness.padicToCoefficient p k a)) =
    UnramifiedCoefficients.coefficientFieldToBCris p j (CoefficientFiniteness.padicToCoefficient p k a)
  rw [coefficientFieldToBCris_padic, Galois.PeriodStructure.bCrisFrobenius_padic]

def coefficientFrobeniusAlg :
    UnramifiedCoefficients.CoefficientField (p := p) (k := k) ≃ₐ[ℚ_[p]] UnramifiedCoefficients.CoefficientField (p := p) (k := k) :=
  { UnramifiedCoefficients.coefficientFrobenius (p := p) (k := k) with commutes' := coefficientFrobenius_padic p j }

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientComparison
