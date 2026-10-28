import OAI.RepresentationTheory.Hecke.Coefficients
import OAI.RepresentationTheory.Hecke.DoubleCoset

/-! # Satake -/

namespace OAI.RepresentationTheory.Hecke.Satake.CosetCalculus

noncomputable section

/-! The normalized integral transform of the two actual double-coset indicators. -/

open _root_.MeasureTheory IsLocalRing
open scoped Classical BigOperators

variable {R F : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [MeasurableSpace F] [MeasurableAdd F] [MeasurableNeg F]

def torusMonomial (α : Fin 3 → ℂˣ) (a : Fin 3 → ℤ) : ℂ :=
  (α 0 : ℂ) ^ a 0 * (α 1 : ℂ) ^ a 1 * (α 2 : ℂ) ^ a 2

def rawDoubleCoset (π : R) (a : Fin 3 → ℤ) (M : CosetCalculusArithmeticMeasure.Mat F) : ℂ :=
  if DoubleCoset.Calculus.InDoubleCoset π a M then 1 else 0

/-- Upper-unipotent integration with each additive integral normalized by vol(O) = 1.
The exponent a₂-a₀ is the square root of the upper Borel modulus. -/
def normalizedSatake (q : ℕ) (π : R) (μ : Measure F) (f : CosetCalculusArithmeticMeasure.Mat F → ℂ)
    (α : Fin 3 → ℂˣ) : ℂ :=
  ∑' a : Fin 3 → ℤ, (q : ℂ) ^ (a 2 - a 0) *
    (∫ x, ∫ z, ∫ y, f (CosetCalculusArithmeticMeasure.triangular (algebraMap R F π) a x y z) ∂μ ∂μ ∂μ) *
      torusMonomial α a

theorem normalized_firstCoefficient [Finite (ResidueField R)]
    (π : R) (hπ : Irreducible π) (μ : Measure F) [μ.IsAddLeftInvariant]
    (hO : MeasurableSet (Set.range (algebraMap R F)))
    (hvol : μ (Set.range (algebraMap R F)) = 1) (a : Fin 3 → ℤ) :
    (Nat.card (ResidueField R) : ℂ) ^ (a 2 - a 0) * Coefficients.CosetCalculus.firstCoefficient π μ a =
      if a = ![1, 0, 0] ∨ a = ![0, 1, 0] ∨ a = ![0, 0, 1]
      then (Nat.card (ResidueField R) : ℂ) else 0 := by
  have hq : (Nat.card (ResidueField R) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ResidueField R)).ne'
  by_cases h1 : a = ![1, 0, 0]
  · subst a
    rw [Coefficients.CosetCalculus.firstCoefficient_formula π hπ μ hO hvol]
    norm_num [Matrix.cons_val_two]
    field_simp
  by_cases h2 : a = ![0, 1, 0]
  · subst a
    rw [Coefficients.CosetCalculus.firstCoefficient_formula π hπ μ hO hvol]
    norm_num [Matrix.cons_val_two]
  by_cases h3 : a = ![0, 0, 1]
  · subst a
    rw [Coefficients.CosetCalculus.firstCoefficient_formula π hπ μ hO hvol]
    norm_num [Matrix.cons_val_two]
  simp [Coefficients.CosetCalculus.firstCoefficient_formula π hπ μ hO hvol, h1, h2, h3]

theorem normalized_secondCoefficient [Finite (ResidueField R)]
    (π : R) (hπ : Irreducible π) (μ : Measure F) [μ.IsAddLeftInvariant]
    (hO : MeasurableSet (Set.range (algebraMap R F)))
    (hvol : μ (Set.range (algebraMap R F)) = 1) (a : Fin 3 → ℤ) :
    (Nat.card (ResidueField R) : ℂ) ^ (a 2 - a 0) * Coefficients.CosetCalculus.secondCoefficient π μ a =
      if a = ![1, 1, 0] ∨ a = ![1, 0, 1] ∨ a = ![0, 1, 1]
      then (Nat.card (ResidueField R) : ℂ) else 0 := by
  have hq : (Nat.card (ResidueField R) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ResidueField R)).ne'
  by_cases h1 : a = ![1, 1, 0]
  · subst a
    rw [Coefficients.CosetCalculus.secondCoefficient_formula π hπ μ hO hvol]
    norm_num [Matrix.cons_val_two]
    field_simp
  by_cases h2 : a = ![1, 0, 1]
  · subst a
    rw [Coefficients.CosetCalculus.secondCoefficient_formula π hπ μ hO hvol]
    norm_num [Matrix.cons_val_two]
  by_cases h3 : a = ![0, 1, 1]
  · subst a
    rw [Coefficients.CosetCalculus.secondCoefficient_formula π hπ μ hO hvol]
    norm_num [Matrix.cons_val_two]
  simp [Coefficients.CosetCalculus.secondCoefficient_formula π hπ μ hO hvol, h1, h2, h3]

theorem satake_first_minuscule [Finite (ResidueField R)]
    (π : R) (hπ : Irreducible π) (μ : Measure F) [μ.IsAddLeftInvariant]
    (hO : MeasurableSet (Set.range (algebraMap R F)))
    (hvol : μ (Set.range (algebraMap R F)) = 1) (α : Fin 3 → ℂˣ) :
    normalizedSatake (Nat.card (ResidueField R)) π μ (rawDoubleCoset π ![1, 0, 0]) α =
      (Nat.card (ResidueField R) : ℂ) * ((α 0 : ℂ) + (α 1 : ℂ) + (α 2 : ℂ)) := by
  unfold normalizedSatake
  simp_rw [rawDoubleCoset, DoubleCoset.Calculus.first_doubleCoset_reversal, ← DoubleCoset.Calculus.firstCondition_iff_doubleCoset π hπ]
  change (∑' a : Fin 3 → ℤ, (Nat.card (ResidueField R) : ℂ) ^ (a 2 - a 0) *
    Coefficients.CosetCalculus.firstCoefficient π μ a * torusMonomial α a) = _
  simp_rw [normalized_firstCoefficient π hπ μ hO hvol]
  rw [tsum_eq_sum (s := {![1, 0, 0], ![0, 1, 0], ![0, 0, 1]}) (fun a ha => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp [ha])]
  norm_num [torusMonomial, Matrix.cons_val_two]
  ring

theorem satake_second_minuscule [Finite (ResidueField R)]
    (π : R) (hπ : Irreducible π) (μ : Measure F) [μ.IsAddLeftInvariant]
    (hO : MeasurableSet (Set.range (algebraMap R F)))
    (hvol : μ (Set.range (algebraMap R F)) = 1) (α : Fin 3 → ℂˣ) :
    normalizedSatake (Nat.card (ResidueField R)) π μ (rawDoubleCoset π ![1, 1, 0]) α =
      (Nat.card (ResidueField R) : ℂ) *
        ((α 0 : ℂ) * (α 1 : ℂ) + (α 0 : ℂ) * (α 2 : ℂ) + (α 1 : ℂ) * (α 2 : ℂ)) := by
  have hp := OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction.uniformizer_map_ne_zero (K := F) hπ
  have hi (a : Fin 3 → ℤ) (x y z : F) :
      DoubleCoset.Calculus.InDoubleCoset π ![1, 1, 0] (CosetCalculusArithmeticMeasure.triangular (algebraMap R F π) a x y z) ↔
        DoubleCoset.Calculus.FirstCondition π (Dual.CosetCalculus.dualMatrix (algebraMap R F π) (CosetCalculusArithmeticMeasure.triangular (algebraMap R F π) a x y z)) := by
    have hdet : (CosetCalculusArithmeticMeasure.triangular (algebraMap R F π) a x y z).det ≠ 0 := by
      rw [CosetCalculusArithmeticMeasure.triangular_det _ hp]
      exact zpow_ne_zero _ hp
    have hc : (fun i : Fin 3 => 1 - (![1, 1, 0] : Fin 3 → ℤ) i) = ![0, 0, 1] := by
      ext i
      fin_cases i <;> rfl
    rw [Dual.CosetCalculus.dual_doubleCoset π hπ ![1, 1, 0] _ hdet, hc, ← DoubleCoset.Calculus.firstCondition_iff_doubleCoset π hπ]
  unfold normalizedSatake
  simp_rw [rawDoubleCoset, hi]
  change (∑' a : Fin 3 → ℤ, (Nat.card (ResidueField R) : ℂ) ^ (a 2 - a 0) *
    Coefficients.CosetCalculus.secondCoefficient π μ a * torusMonomial α a) = _
  simp_rw [normalized_secondCoefficient π hπ μ hO hvol]
  rw [tsum_eq_sum (s := {![1, 1, 0], ![1, 0, 1], ![0, 1, 1]}) (fun a ha => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp [ha])]
  norm_num [torusMonomial, Matrix.cons_val_two]
  ring

end

end OAI.RepresentationTheory.Hecke.Satake.CosetCalculus
