import OAI.RepresentationTheory.Hecke.Dual
import OAI.RepresentationTheory.Hecke.CosetCalculusArithmeticMeasure

/-! # Coefficients -/

namespace OAI.RepresentationTheory.Hecke.Coefficients.CosetCalculus

noncomputable section

/-! Actual unipotent integrals, before multiplication by the modulus factor. -/

open _root_.MeasureTheory IsLocalRing
open scoped Classical

variable {R F : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [MeasurableSpace F] [MeasurableAdd F] [MeasurableNeg F]

def firstCoefficient (π : R) (μ : Measure F) (a : Fin 3 → ℤ) : ℂ :=
  ∫ x, ∫ z, ∫ y, if DoubleCoset.Calculus.FirstCondition π (CosetCalculusArithmeticMeasure.triangular (algebraMap R F π) a x y z)
    then (1 : ℂ) else 0 ∂μ ∂μ ∂μ

def secondCoefficient (π : R) (μ : Measure F) (a : Fin 3 → ℤ) : ℂ :=
  ∫ x, ∫ z, ∫ y, if DoubleCoset.Calculus.FirstCondition π
    (Dual.CosetCalculus.dualMatrix (algebraMap R F π) (CosetCalculusArithmeticMeasure.triangular (algebraMap R F π) a x y z))
    then (1 : ℂ) else 0 ∂μ ∂μ ∂μ

theorem firstCoefficient_formula [Finite (ResidueField R)]
    (π : R) (hπ : Irreducible π) (μ : Measure F) [μ.IsAddLeftInvariant]
    (hO : MeasurableSet (Set.range (algebraMap R F)))
    (hvol : μ (Set.range (algebraMap R F)) = 1) (a : Fin 3 → ℤ) :
    firstCoefficient π μ a =
      if a = ![1, 0, 0] then (Nat.card (ResidueField R) : ℂ) ^ 2 else
      if a = ![0, 1, 0] then (Nat.card (ResidueField R) : ℂ) else
      if a = ![0, 0, 1] then 1 else 0 := by
  let O : Set F := Set.range (algebraMap R F)
  let B : Set F := CosetCalculusArithmeticMeasure.integralBall π
  have hB : MeasurableSet B := by
    rw [show B = ⋃ a : ResidueField R, CosetCalculusArithmeticMeasure.residueCoset π a from CosetCalculusArithmeticMeasure.integralBall_eq_union π hπ]
    exact MeasurableSet.iUnion (fun a => CosetCalculusArithmeticMeasure.measurable_residueCoset π a hO)
  have vO : CosetCalculusArithmeticMeasure.complexVolume μ O = 1 := by
    simp [CosetCalculusArithmeticMeasure.complexVolume, measureReal_def, O, hvol]
  have vB : CosetCalculusArithmeticMeasure.complexVolume μ B = (Nat.card (ResidueField R) : ℂ) := by
    simp [CosetCalculusArithmeticMeasure.complexVolume, measureReal_def, B, CosetCalculusArithmeticMeasure.measure_integralBall π hπ μ hO hvol]
  have h100 : firstCoefficient π μ ![1, 0, 0] = (Nat.card (ResidueField R) : ℂ) ^ 2 := by
    unfold firstCoefficient
    simp_rw [Dual.CosetCalculus.firstCondition_triangular π hπ]
    norm_num
    change (∫ x, ∫ z, ∫ y, if x ∈ B ∧ y ∈ B ∧ z ∈ O then (1 : ℂ) else 0 ∂μ ∂μ ∂μ) = _
    rw [CosetCalculusArithmeticMeasure.integral_box μ B B O hB hB hO, vO, vB]
    ring
  have h010 : firstCoefficient π μ ![0, 1, 0] = (Nat.card (ResidueField R) : ℂ) := by
    unfold firstCoefficient
    simp_rw [Dual.CosetCalculus.firstCondition_triangular π hπ]
    norm_num
    change (∫ x, ∫ z, ∫ y, if x ∈ O ∧ y ∈ O ∧ z ∈ B then (1 : ℂ) else 0 ∂μ ∂μ ∂μ) = _
    rw [CosetCalculusArithmeticMeasure.integral_box μ O O B hO hO hB, vO, vB]
    ring
  have h001 : firstCoefficient π μ ![0, 0, 1] = 1 := by
    unfold firstCoefficient
    simp_rw [Dual.CosetCalculus.firstCondition_triangular π hπ]
    norm_num
    change (∫ x, ∫ z, ∫ y, if x ∈ O ∧ y ∈ O ∧ z ∈ O then (1 : ℂ) else 0 ∂μ ∂μ ∂μ) = _
    rw [CosetCalculusArithmeticMeasure.integral_box μ O O O hO hO hO, vO]
    ring
  by_cases h1 : a = ![1, 0, 0]
  · subst a
    simpa using h100
  by_cases h2 : a = ![0, 1, 0]
  · subst a
    simpa using h010
  by_cases h3 : a = ![0, 0, 1]
  · subst a
    simpa using h001
  simp [firstCoefficient, Dual.CosetCalculus.firstCondition_triangular π hπ, h1, h2, h3]

theorem secondCoefficient_formula [Finite (ResidueField R)]
    (π : R) (hπ : Irreducible π) (μ : Measure F) [μ.IsAddLeftInvariant]
    (hO : MeasurableSet (Set.range (algebraMap R F)))
    (hvol : μ (Set.range (algebraMap R F)) = 1) (a : Fin 3 → ℤ) :
    secondCoefficient π μ a =
      if a = ![1, 1, 0] then (Nat.card (ResidueField R) : ℂ) ^ 2 else
      if a = ![1, 0, 1] then (Nat.card (ResidueField R) : ℂ) else
      if a = ![0, 1, 1] then 1 else 0 := by
  let O : Set F := Set.range (algebraMap R F)
  let B : Set F := CosetCalculusArithmeticMeasure.integralBall π
  have hB : MeasurableSet B := by
    rw [show B = ⋃ a : ResidueField R, CosetCalculusArithmeticMeasure.residueCoset π a from CosetCalculusArithmeticMeasure.integralBall_eq_union π hπ]
    exact MeasurableSet.iUnion (fun a => CosetCalculusArithmeticMeasure.measurable_residueCoset π a hO)
  have vO : CosetCalculusArithmeticMeasure.complexVolume μ O = 1 := by
    simp [CosetCalculusArithmeticMeasure.complexVolume, measureReal_def, O, hvol]
  have vB : CosetCalculusArithmeticMeasure.complexVolume μ B = (Nat.card (ResidueField R) : ℂ) := by
    simp [CosetCalculusArithmeticMeasure.complexVolume, measureReal_def, B, CosetCalculusArithmeticMeasure.measure_integralBall π hπ μ hO hvol]
  have nO : ∀ x : F, -x ∈ O ↔ x ∈ O := fun x => Dual.CosetCalculus.integralElement_neg x
  have nB : ∀ x : F, -x ∈ B ↔ x ∈ B := by
    intro x
    change CosetCalculusArithmeticMeasure.IntegralElement (R := R) (algebraMap R F π * -x) ↔ _
    rw [mul_neg, Dual.CosetCalculus.integralElement_neg]
    rfl
  have h110 : secondCoefficient π μ ![1, 1, 0] = (Nat.card (ResidueField R) : ℂ) ^ 2 := by
    unfold secondCoefficient
    simp_rw [Dual.CosetCalculus.secondCondition_triangular π hπ]
    norm_num
    change (∫ x, ∫ z, ∫ y, if x ∈ O ∧ x * z - y ∈ B ∧ z ∈ B then (1 : ℂ) else 0 ∂μ ∂μ ∂μ) = _
    rw [CosetCalculusArithmeticMeasure.integral_twisted_box μ O B B hO hB hB nB, vO, vB]
    ring
  have h101 : secondCoefficient π μ ![1, 0, 1] = (Nat.card (ResidueField R) : ℂ) := by
    unfold secondCoefficient
    simp_rw [Dual.CosetCalculus.secondCondition_triangular π hπ]
    norm_num
    change (∫ x, ∫ z, ∫ y, if x ∈ B ∧ x * z - y ∈ O ∧ z ∈ O then (1 : ℂ) else 0 ∂μ ∂μ ∂μ) = _
    rw [CosetCalculusArithmeticMeasure.integral_twisted_box μ B O O hB hO hO nO, vO, vB]
    ring
  have h011 : secondCoefficient π μ ![0, 1, 1] = 1 := by
    unfold secondCoefficient
    simp_rw [Dual.CosetCalculus.secondCondition_triangular π hπ]
    norm_num
    change (∫ x, ∫ z, ∫ y, if x ∈ O ∧ x * z - y ∈ O ∧ z ∈ O then (1 : ℂ) else 0 ∂μ ∂μ ∂μ) = _
    rw [CosetCalculusArithmeticMeasure.integral_twisted_box μ O O O hO hO hO nO, vO]
    ring
  by_cases h1 : a = ![1, 1, 0]
  · subst a
    simpa using h110
  by_cases h2 : a = ![1, 0, 1]
  · subst a
    simpa using h101
  by_cases h3 : a = ![0, 1, 1]
  · subst a
    simpa using h011
  simp [secondCoefficient, Dual.CosetCalculus.secondCondition_triangular π hπ, h1, h2, h3]

end

end OAI.RepresentationTheory.Hecke.Coefficients.CosetCalculus
