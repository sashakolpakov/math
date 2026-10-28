import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GradedClassification
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.GradedRelations
import Mathlib.Algebra.Module.FinitePresentation

/-! # Ideal Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated

noncomputable section

/-!
A finite compatible tuple extends to the actual homogeneous ideal generated
by its retained degrees. Every retained degree is recovered exactly. Higher
degree flatness is not asserted by this construction.
-/

universe u v

variable {R : Type u} [CommRing R] {σ : Type v} {B : ℕ} {r : ℕ → ℕ}
variable (D : GradedClassification.TruncatedGradedQuotientData R σ B r)

def GradedClassification.TruncatedGradedQuotientData.extensionPiece : ∀ d, Submodule R (MvPolynomial.homogeneousSubmodule σ R d)
  | 0 => (D.quotient ⟨0, Nat.zero_lt_succ B⟩).toSubmodule
  | d + 1 => if h : d + 1 ≤ B then
      (D.quotient ⟨d + 1, Nat.lt_succ_of_le h⟩).toSubmodule
    else ⨆ i : σ, (extensionPiece d).map (Homogeneous.MultiplicationMatrices.homogeneousMultiplyX R σ d i)

theorem GradedClassification.TruncatedGradedQuotientData.extensionPiece_retained (d : ℕ) (hd : d ≤ B) :
    D.extensionPiece d = (D.quotient ⟨d, Nat.lt_succ_of_le hd⟩).toSubmodule := by
  cases d with
  | zero => rfl
  | succ d => simp only [GradedClassification.TruncatedGradedQuotientData.extensionPiece, dite_eq_left hd]

theorem GradedClassification.TruncatedGradedQuotientData.extensionPiece_generated (d : ℕ) (hd : B ≤ d) :
    D.extensionPiece (d + 1) =
      ⨆ i : σ, (D.extensionPiece d).map (Homogeneous.MultiplicationMatrices.homogeneousMultiplyX R σ d i) := by
  simp only [GradedClassification.TruncatedGradedQuotientData.extensionPiece, dite_eq_right (show ¬d + 1 ≤ B by omega)]

theorem GradedClassification.TruncatedGradedQuotientData.extensionPiece_variable_mul (d : ℕ) (i : σ) :
    D.extensionPiece d ≤ (D.extensionPiece (d + 1)).comap (Homogeneous.MultiplicationMatrices.homogeneousMultiplyX R σ d i) := by
  by_cases hd : d + 1 ≤ B
  · rw [D.extensionPiece_retained d (by omega), D.extensionPiece_retained (d + 1) hd]
    exact D.variable_mul ⟨d, by omega⟩ i
  · rw [D.extensionPiece_generated d (by omega)]
    exact Submodule.map_le_iff_le_comap.mp
      (le_iSup (fun j : σ => (D.extensionPiece d).map (Homogeneous.MultiplicationMatrices.homogeneousMultiplyX R σ d j)) i)

def GradedClassification.TruncatedGradedQuotientData.generatedRelations : GradedIdealReconstruction.GradedIdealRelations R σ where
  piece := D.extensionPiece
  variable_mul := D.extensionPiece_variable_mul

def GradedClassification.TruncatedGradedQuotientData.generatedIdeal : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R) :=
  D.generatedRelations.toHomogeneousIdeal

theorem GradedClassification.TruncatedGradedQuotientData.generatedIdeal_degree (d : Fin (B + 1)) :
    Homogeneous.IdealIncidence.homogeneousDegreeRelations D.generatedIdeal d = (D.quotient d).toSubmodule :=
  (D.generatedRelations.toHomogeneousIdeal_degree d).trans
    (D.extensionPiece_retained d (Nat.le_of_lt_succ d.isLt))

theorem GradedClassification.TruncatedGradedQuotientData.generatedIdeal_generated : D.generatedRelations.lowDegreeIdeal B = D.generatedIdeal.toIdeal :=
  D.generatedRelations.lowDegreeIdeal_eq B D.extensionPiece_generated

variable [Finite σ]

theorem GradedClassification.TruncatedGradedQuotientData.retainedRelations_fg (d : Fin (B + 1)) : (D.quotient d).toSubmodule.FG := by
  let N := (D.quotient d).toSubmodule
  let : Module.Finite R (MvPolynomial.homogeneousSubmodule σ R d) :=
    Module.Finite.of_basis (Homogeneous.Coordinates.homogeneousMonomialBasis R σ d)
  let : Module.FinitePresentation R (MvPolynomial.homogeneousSubmodule σ R d ⧸ N) :=
    Module.finitePresentation_of_projective _ _
  have h := Module.FinitePresentation.fg_ker N.mkQ N.mkQ_surjective
  rw [Submodule.ker_mkQ] at h
  exact h

theorem GradedClassification.TruncatedGradedQuotientData.generatedIdeal_fg : D.generatedIdeal.toIdeal.FG := by
  apply D.generatedRelations.toIdeal_fg_of_generated B D.extensionPiece_generated
  intro d hd
  change (D.extensionPiece d).FG
  rw [D.extensionPiece_retained d hd]
  exact D.retainedRelations_fg ⟨d, Nat.lt_succ_of_le hd⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated
