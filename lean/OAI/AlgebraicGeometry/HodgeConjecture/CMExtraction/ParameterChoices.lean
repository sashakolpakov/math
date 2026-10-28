import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd
import OAI.NumberTheory.CMField.NormOneApproximation
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Parameter Choices -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ParameterChoices

noncomputable section

/-!
# Concrete choices for the GaloisValuation parameter construction

The CM type selects representatives, and normal restriction constructs the
Galois map for an actual embedding in the algebraic closure. NormOneApproximation constructs
the norm-one scalar using the proved finiteness of the number-field class
group. Identifying the geometric completely split prime with its local
valuation remains a separate step.
-/

open scoped Classical
open _root_.NumberField IsDedekindDomain

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]

def representatives (v : Multiplicity.Odd.Sign E) : Finset Gal(E/ℚ) :=
  Finset.univ.filter (fun τ => v.val τ = true)

omit [IsGalois ℚ E] in
theorem representatives_active (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true) :
    (1 : Gal(E/ℚ)) ∈ representatives E v := by
  simp only [representatives, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hv

omit [IsGalois ℚ E] in
theorem representatives_paired (v : Multiplicity.Odd.Sign E) (τ : Gal(E/ℚ)) :
    τ ∈ representatives E v ↔ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∉ representatives E v := by
  simp only [representatives, Finset.mem_filter, Finset.mem_univ, true_and,
    v.property τ]
  cases v.val τ <;> decide

abbrev Qbar := AlgebraicClosure ℚ

def algebraicEmbedding : E →ₐ[ℚ] Qbar := IsAlgClosed.lift

def restriction (ι : E →ₐ[ℚ] Qbar) : Gal(Qbar/ℚ) →* Gal(E/ℚ) := by
  let : Algebra E Qbar := ι.toAlgebra
  let : IsScalarTower ℚ E Qbar := IsScalarTower.of_algebraMap_eq
    (fun x => (ι.commutes x).symm)
  exact AlgEquiv.restrictNormalHom E

omit [NumberField E] [NumberField.IsCMField E] in
theorem restriction_commutes (ι : E →ₐ[ℚ] Qbar) (σ : Gal(Qbar/ℚ)) (x : E) :
    σ (ι x) = ι ((restriction E ι σ) x) := by
  let : Algebra E Qbar := ι.toAlgebra
  let : IsScalarTower ℚ E Qbar := IsScalarTower.of_algebraMap_eq
    (fun x => (ι.commutes x).symm)
  exact (AlgEquiv.restrictNormal_commutes σ E x).symm

omit [NumberField E] [NumberField.IsCMField E] in
theorem restriction_surjective (ι : E →ₐ[ℚ] Qbar) :
    Function.Surjective (restriction E ι) := by
  let : Algebra.IsAlgebraic ℚ Qbar := AlgebraicClosure.isAlgebraic ℚ
  let : Normal ℚ Qbar :=
    { isAlgebraic := Algebra.IsAlgebraic.isAlgebraic
      splits' := fun x => IsAlgClosed.splits _ }
  let : Algebra E Qbar := ι.toAlgebra
  let : IsScalarTower ℚ E Qbar := IsScalarTower.of_algebraMap_eq
    (fun x => (ι.commutes x).symm)
  exact AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := E) Qbar

theorem exists_split_scalar
    (w wbar : HeightOneSpectrum (𝓞 E))
    (hconj : wbar.asIdeal = Ideal.map
      (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom w.asIdeal)
    (hsplit : w ≠ wbar) :
    ∃ (r : Eˣ) (M : ℕ), 0 < M ∧
      (r : E) * NumberField.IsCMField.complexConj E (r : E) = 1 ∧
      w.valuation E (r : E) = WithZero.exp (-(M : ℤ)) ∧
      wbar.valuation E (r : E) = WithZero.exp (M : ℤ) ∧
      (∀ p : HeightOneSpectrum (𝓞 E),
        p ≠ w → p ≠ wbar → p.valuation E (r : E) = 1) ∧
      (∀ (S : Finset (HeightOneSpectrum (𝓞 E)))
          (depth : HeightOneSpectrum (𝓞 E) → ℕ), w ∉ S → wbar ∉ S →
        ∃ N : ℕ, 0 < N ∧ ∀ p ∈ S,
          p.valuation E ((r : E) ^ N - 1) ≤ WithZero.exp (-(depth p : ℤ))) :=
  OAI.NumberTheory.CMField.NormOneApproximation.Construction.exists_norm_one_scalar inferInstance w wbar hconj hsplit

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ParameterChoices
