import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization
import OAI.RepresentationTheory.Weil.Local.LinearIntertwiner
import OAI.RepresentationTheory.Theta.Adelic.SplitUnitary
import OAI.RepresentationTheory.Weil.Local.DeterminantMeasure

/-! # Levi Cayley Phase -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.LeviCayleyPhase

/-! The corrected Cayley phase on a Levi element, expressed in the
position and momentum variables used by Fourier inversion. -/

open _root_.Matrix

open OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization.Construction OAI.RepresentationTheory.Theta.Adelic.SplitUnitary

variable {k : Type} [NormedField k] [CharZero k] (N : ℕ)
variable (A U : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N) (hU : U.val = A.val - 1)

def momentumDifference : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N := -SplitUnitary.transposeUnit (U * A⁻¹)

include hU in
omit [CharZero k] in
theorem momentumDifference_val : (momentumDifference N A U).val = (A⁻¹).val.transpose - 1 := by
  change -(U.val * (A⁻¹).val).transpose = _
  rw [hU, sub_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul,
    Matrix.transpose_sub, Matrix.transpose_one]
  abel

def differenceUnit : (Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) k)ˣ where
  val := Matrix.fromBlocks U.val 0 0 (momentumDifference N A U).val
  inv := Matrix.fromBlocks U.inv 0 0 (momentumDifference N A U).inv
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

include hU in
omit [CharZero k] in
theorem differenceUnit_val : (differenceUnit N A U).val = (Weil.Local.Generators.Construction.leviSymplectic A).val - 1 := by
  change Matrix.fromBlocks U.val 0 0 (momentumDifference N A U).val =
    Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose - 1
  rw [momentumDifference_val N A U hU, hU]
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.one_apply]

include hU in
omit [CharZero k] in
theorem levi_openCell : ((Weil.Local.Generators.Construction.leviSymplectic A).val - 1).det ≠ 0 := by
  rw [← differenceUnit_val N A U hU]
  exact (Matrix.GeneralLinearGroup.det (differenceUnit N A U)).ne_zero

include hU in
omit [CharZero k] in
theorem inverse_difference_sumElim (q p : Weil.Local.FunctionsMetaplectic.Construction.Position k N) :
    (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference k N (Weil.Local.Generators.Construction.leviSymplectic A) (levi_openCell N A U hU)).symm (Sum.elim q p) =
      Sum.elim ((U⁻¹).val.mulVec q) (-((A.val.transpose * (U⁻¹).val.transpose).mulVec p)) := by
  apply (Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference k N (Weil.Local.Generators.Construction.leviSymplectic A) (levi_openCell N A U hU)).injective
  rw [LinearEquiv.apply_symm_apply, Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference_apply]
  change Sum.elim q p = (Weil.Local.Generators.Construction.leviSymplectic A).val.mulVec _ - _
  nth_rw 2 [← Matrix.one_mulVec (Sum.elim ((U⁻¹).val.mulVec q)
    (-((A.val.transpose * (U⁻¹).val.transpose).mulVec p)))]
  rw [← Matrix.sub_mulVec, ← differenceUnit_val N A U hU]
  change Sum.elim q p = (Matrix.fromBlocks U.val 0 0 (momentumDifference N A U).val).mulVec _
  have hp : (momentumDifference N A U).val * (-(A.val.transpose * (U⁻¹).val.transpose)) = 1 := by
    change (-(U.val * (A⁻¹).val).transpose) * (-(A.val.transpose * (U⁻¹).val.transpose)) = 1
    rw [neg_mul_neg, Matrix.transpose_mul]
    calc
      _ = ((A⁻¹).val.transpose * (U.val.transpose * A.val.transpose)) * (U⁻¹).val.transpose := by
        simp only [mul_assoc]
      _ = 1 := by
        have hc : U.val * A.val = A.val * U.val := by rw [hU]; noncomm_ring
        have hct := congrArg Matrix.transpose hc
        rw [Matrix.transpose_mul, Matrix.transpose_mul] at hct
        rw [← hct]
        simp only [← Matrix.transpose_mul, ← Units.val_mul]
        simp
  rw [Matrix.fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec, add_zero, zero_add]
  apply congrArg₂ Sum.elim
  · rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  · rw [← Matrix.neg_mulVec, Matrix.mulVec_mulVec, hp, Matrix.one_mulVec]

omit [CharZero k] in
theorem schrodingerPairing_sumElim (q p q' p' : Weil.Local.FunctionsMetaplectic.Construction.Position k N) :
    Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerPairing k N (Sum.elim q p) (Sum.elim q' p') = Weil.Local.FunctionsMetaplectic.Construction.dot p q' - Weil.Local.FunctionsMetaplectic.Construction.dot q p' := by
  rw [Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerPairing_eq_standard]
  simp only [Weil.UnitarySplitting.Oscillator.Construction.standardSymplecticPairing, Sum.elim_inl,
    Sum.elim_inr, Finset.sum_sub_distrib, Weil.Local.FunctionsMetaplectic.Construction.dot]

include hU in
theorem cayleyPhase_levi (q p : Weil.Local.FunctionsMetaplectic.Construction.Position k N) :
    Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerCayleyPhase k N (Weil.Local.Generators.Construction.leviSymplectic A) (levi_openCell N A U hU) (Sum.elim q p) -
      Weil.Local.FunctionsMetaplectic.Construction.dot p q / 2 = -Weil.Local.FunctionsMetaplectic.Construction.dot p ((A.val * (U⁻¹).val).mulVec q) := by
  change Weil.AdelicSplitting.SchrodingerPairing.Construction.schrodingerPairing k N
    ((Weil.AdelicSplitting.SchrodingerPairing.Construction.openCellDifference k N (Weil.Local.Generators.Construction.leviSymplectic A) (levi_openCell N A U hU)).symm (Sum.elim q p))
    (Sum.elim q p) / 2 - Weil.Local.FunctionsMetaplectic.Construction.dot p q / 2 = _
  rw [inverse_difference_sumElim N A U hU, schrodingerPairing_sumElim]
  have hc : A.val * (U⁻¹).val = (U⁻¹).val * A.val := by
    have hucomm : Commute U A := by
      apply Units.ext
      change U.val * A.val = A.val * U.val
      rw [hU]
      noncomm_ring
    exact congrArg Units.val hucomm.inv_left.eq.symm
  have hdiff : (A.val * (U⁻¹).val).mulVec q - (U⁻¹).val.mulVec q = q := by
    have hm : A.val * (U⁻¹).val - (U⁻¹).val = 1 := by
      calc
        _ = (A.val - 1) * (U⁻¹).val := by noncomm_ring
        _ = 1 := by rw [← hU, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [← Matrix.sub_mulVec, hm, Matrix.one_mulVec]
  have hdot : Weil.Local.FunctionsMetaplectic.Construction.dot p ((A.val * (U⁻¹).val).mulVec q) - Weil.Local.FunctionsMetaplectic.Construction.dot p ((U⁻¹).val.mulVec q) = Weil.Local.FunctionsMetaplectic.Construction.dot p q := by
    change p ⬝ᵥ ((A.val * (U⁻¹).val).mulVec q) - p ⬝ᵥ ((U⁻¹).val.mulVec q) = p ⬝ᵥ q
    rw [← dotProduct_sub]
    exact congrArg (Weil.Local.FunctionsMetaplectic.Construction.dot p) hdiff
  change ((-((A.val.transpose * (U⁻¹).val.transpose).mulVec p)) ⬝ᵥ q -
      ((U⁻¹).val.mulVec q) ⬝ᵥ p) / 2 - Weil.Local.FunctionsMetaplectic.Construction.dot p q / 2 = _
  rw [neg_dotProduct, ← Matrix.transpose_mul,
    dotProduct_comm (((U⁻¹).val * A.val).transpose.mulVec p) q,
    Matrix.dotProduct_transpose_mulVec, ← hc,
    dotProduct_comm ((U⁻¹).val.mulVec q) p]
  change (-Weil.Local.FunctionsMetaplectic.Construction.dot p ((A.val * (U⁻¹).val).mulVec q) - Weil.Local.FunctionsMetaplectic.Construction.dot p ((U⁻¹).val.mulVec q)) / 2 - Weil.Local.FunctionsMetaplectic.Construction.dot p q / 2 = _
  rw [← hdot]
  ring

end RepresentationTheory.Theta.Adelic.LeviCayleyPhase

namespace RepresentationTheory.Theta.Adelic.LeviCayleyPhase.Scale

/-! The exact Haar factor of a Levi open cell. -/

open scoped NNReal

open OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedNormalization.Construction OAI.RepresentationTheory.Theta.Adelic.LeviCayleyPhase

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
variable [MeasurableSpace k] [BorelSpace k]

omit [MeasurableSpace k] [BorelSpace k] in
theorem haarModulus_neg_one : Weil.Local.DeterminantMeasure.Construction.haarModulus k (-1) = 1 := by
  apply NNReal.coe_injective
  have hs : (Weil.Local.DeterminantMeasure.Construction.haarModulus k (-1) : ℝ) ^ 2 = 1 := by
    have h : Weil.Local.DeterminantMeasure.Construction.haarModulus k (-1) ^ 2 = 1 := by rw [← map_pow]; simp
    exact_mod_cast h
  have hn : 0 ≤ (Weil.Local.DeterminantMeasure.Construction.haarModulus k (-1) : ℝ) := NNReal.coe_nonneg _
  change (Weil.Local.DeterminantMeasure.Construction.haarModulus k (-1) : ℝ) = 1
  nlinarith

omit [MeasurableSpace k] [BorelSpace k] in
theorem haarModulus_neg (a : k) : Weil.Local.DeterminantMeasure.Construction.haarModulus k (-a) = Weil.Local.DeterminantMeasure.Construction.haarModulus k a := by
  rw [← neg_one_mul a, map_mul, haarModulus_neg_one, one_mul]

variable (N : ℕ) (A U : Weil.Local.FunctionsMetaplectic.Construction.GeneralLinear k N) (hU : U.val = A.val - 1)

include hU in
omit [MeasurableSpace k] [BorelSpace k] in
theorem levi_difference_modulus :
    (Weil.Local.DeterminantMeasure.Construction.haarModulus k ((Weil.Local.Generators.Construction.leviSymplectic A).val - 1).det : ℝ) =
      Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k U) ^ 2 / Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k A) := by
  rw [← differenceUnit_val N A U hU]
  change (Weil.Local.DeterminantMeasure.Construction.haarModulus k (Matrix.fromBlocks U.val 0 0 (momentumDifference N A U).val).det : ℝ) = _
  rw [Matrix.det_fromBlocks_zero₂₁]
  change (Weil.Local.DeterminantMeasure.Construction.haarModulus k (U.val.det * (-(U.val * (A⁻¹).val).transpose).det) : ℝ) = _
  have hAinv : (A⁻¹).val.det = A.val.det⁻¹ := by
    change (Matrix.GeneralLinearGroup.det A⁻¹).val = _
    rw [map_inv, Units.val_inv_eq_inv_val]
    rfl
  rw [Matrix.det_neg, Matrix.det_transpose, Matrix.det_mul, hAinv]
  simp only [map_mul, map_pow, haarModulus_neg_one, one_pow, one_mul,
    NNReal.coe_mul, map_inv₀, NNReal.coe_inv]
  have hUδ : (Weil.Local.DeterminantMeasure.Construction.haarModulus k U.val.det : ℝ) = Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k U) :=
    congrArg (fun x : ℝ≥0 => (x : ℝ)) (Weil.Local.DeterminantMeasure.Construction.haarModulus_unit k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k U))
  have hAδ : (Weil.Local.DeterminantMeasure.Construction.haarModulus k A.val.det : ℝ) = Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k A) :=
    congrArg (fun x : ℝ≥0 => (x : ℝ)) (Weil.Local.DeterminantMeasure.Construction.haarModulus_unit k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k A))
  rw [hUδ, hAδ]
  ring

include hU in
omit [MeasurableSpace k] [BorelSpace k] in
theorem openCellScale_levi :
    Weil.AdelicSplitting.Normalization.Construction.openCellScale k N (Weil.Local.Generators.Construction.leviSymplectic A) =
      Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k U) / Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Weil.Local.FunctionsMetaplectic.Construction.determinantUnit k A)) := by
  rw [Weil.AdelicSplitting.Normalization.Construction.openCellScale, dite_eq_left (levi_openCell N A U hU)]
  have hh : Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Units.mk0 ((Weil.Local.Generators.Construction.leviSymplectic A).val - 1).det (levi_openCell N A U hU)) =
      (Weil.Local.DeterminantMeasure.Construction.haarModulus k ((Weil.Local.Generators.Construction.leviSymplectic A).val - 1).det : ℝ) :=
    (congrArg (fun x : ℝ≥0 => (x : ℝ))
      (Weil.Local.DeterminantMeasure.Construction.haarModulus_unit k (Units.mk0 _ (levi_openCell N A U hU)))).symm
  rw [hh, levi_difference_modulus N A U hU,
    Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (Weil.Local.FunctionsMetaplectic.Construction.localModulus_pos k _).le]

end RepresentationTheory.Theta.Adelic.LeviCayleyPhase.Scale

end

end OAI
