import OAI.Analysis.DifferentialForms.Manifold.CovectorAction
import OAI.Analysis.DifferentialForms.Manifold.Derivative
import Mathlib.Tactic.Module

/-! # Dolbeault Projection -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.DolbeaultProjection

noncomputable section

/-!
# Smooth projections of the derivative of a pure manifold form

On a pure `(p,q)` input, the two neighboring components of its derivative
have opposite eigenvalues for scalar pullback by `I`. The formulas below
use the actual smooth tangent-scalar action to construct both projections.
Their identification with the local Dolbeault differential is proved in
the subsequent local-to-global comparison.
-/

open scoped _root_.Manifold ContDiff

/-- The genuine nonzero complex scalar used to separate adjacent bidegrees. -/
def dolbeaultIUnit : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero

@[simp]
theorem dolbeaultIUnit_coe : (dolbeaultIUnit : ℂ) = Complex.I := rfl

/-- The direct scalar-pullback eigenvalue of the prime component. -/
def dolbeaultPrimeCharacter (p q : ℕ) : ℂ :=
  Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter (p + 1) q dolbeaultIUnit

theorem dolbeaultPrimeCharacter_ne_zero (p q : ℕ) :
    dolbeaultPrimeCharacter p q ≠ 0 := by
  unfold dolbeaultPrimeCharacter Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter
  exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero dolbeaultIUnit))
    (pow_ne_zero _ (star_ne_zero.mpr (Units.ne_zero dolbeaultIUnit)))

/-- The double-prime component has the opposite eigenvalue. -/
theorem dolbeaultDoublePrimeCharacter (p q : ℕ) :
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p (q + 1) dolbeaultIUnit = -dolbeaultPrimeCharacter p q := by
  simp only [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, dolbeaultPrimeCharacter, dolbeaultIUnit_coe,
    Complex.star_def, Complex.conj_I, pow_succ]
  ring

/-- The explicit prime projector selects the first of the two neighboring characters. -/
theorem dolbeaultPrimeProjection_of_characters
    {V : Type*} [AddCommGroup V] [Module ℂ V] (p q : ℕ) (T : V →ₗ[ℂ] V)
    (A B : V) (hA : T A = dolbeaultPrimeCharacter p q • A)
    (hB : T B = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p (q + 1) dolbeaultIUnit • B) :
    (1 / 2 : ℂ) • (A + B + (dolbeaultPrimeCharacter p q)⁻¹ • T (A + B)) = A := by
  rw [map_add, hA, hB, dolbeaultDoublePrimeCharacter]
  simp only [smul_add, smul_smul, inv_mul_cancel₀ (dolbeaultPrimeCharacter_ne_zero p q),
    one_smul, neg_smul, smul_neg]
  module

/-- The explicit double-prime projector selects the other neighboring character. -/
theorem dolbeaultDoublePrimeProjection_of_characters
    {V : Type*} [AddCommGroup V] [Module ℂ V] (p q : ℕ) (T : V →ₗ[ℂ] V)
    (A B : V) (hA : T A = dolbeaultPrimeCharacter p q • A)
    (hB : T B = Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p (q + 1) dolbeaultIUnit • B) :
    (1 / 2 : ℂ) • (A + B - (dolbeaultPrimeCharacter p q)⁻¹ • T (A + B)) = B := by
  rw [map_add, hA, hB, dolbeaultDoublePrimeCharacter]
  simp only [smul_add, smul_smul, inv_mul_cancel₀ (dolbeaultPrimeCharacter_ne_zero p q),
    one_smul, neg_smul, smul_neg]
  module

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] (M : Type*) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

/-- The prime projection of the actual derivative of a pure manifold form. -/
def manifoldDolbeaultPrimeForm (p q : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + q + 1) :=
  (1 / 2 : ℂ) •
    ((Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d + (dolbeaultPrimeCharacter p q)⁻¹ •
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction (dolbeaultIUnit⁻¹)).comp Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d).comp
        (Analysis.DifferentialForms.Manifold.ManifoldBidegree.pureManifoldFormSubmodule E M p q).subtype)

/-- The double-prime projection of the actual derivative of a pure manifold form. -/
def manifoldDolbeaultDoublePrimeForm (p q : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + q + 1) :=
  (1 / 2 : ℂ) •
    ((Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d - (dolbeaultPrimeCharacter p q)⁻¹ •
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction (dolbeaultIUnit⁻¹)).comp Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d).comp
        (Analysis.DifferentialForms.Manifold.ManifoldBidegree.pureManifoldFormSubmodule E M p q).subtype)

@[simp]
theorem manifoldDolbeaultPrimeForm_apply (p q : ℕ) (form : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q) :
    manifoldDolbeaultPrimeForm E M p q form =
      (1 / 2 : ℂ) • (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form.1 +
        (dolbeaultPrimeCharacter p q)⁻¹ •
          Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction (dolbeaultIUnit⁻¹) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form.1)) := rfl

@[simp]
theorem manifoldDolbeaultDoublePrimeForm_apply (p q : ℕ) (form : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q) :
    manifoldDolbeaultDoublePrimeForm E M p q form =
      (1 / 2 : ℂ) • (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form.1 -
        (dolbeaultPrimeCharacter p q)⁻¹ •
          Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.complexAction (dolbeaultIUnit⁻¹) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form.1)) := rfl

/-- The two explicitly constructed smooth projections add to the genuine derivative. -/
theorem manifoldDolbeaultPrimeForm_add_doublePrime (p q : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q) :
    manifoldDolbeaultPrimeForm E M p q form + manifoldDolbeaultDoublePrimeForm E M p q form =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form.1 := by
  rw [manifoldDolbeaultPrimeForm_apply, manifoldDolbeaultDoublePrimeForm_apply]
  module

variable {E M}

/-- In a holomorphic chart the prime projection uses the ordinary scalar
pullback on the actual derivative of the coefficient form. -/
theorem manifoldDolbeaultPrimeForm_inChart (p q : ℕ) (form : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) {y : E} (hy : y ∈ e.target) :
    (manifoldDolbeaultPrimeForm E M p q form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 1)).inChart e y =
      (1 / 2 : ℂ) •
        (extDeriv ((form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q)).inChart e) y +
          (dolbeaultPrimeCharacter p q)⁻¹ •
            Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback E (p + q + 1) Complex.I
              (extDeriv ((form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q)).inChart e) y)) := by
  rw [manifoldDolbeaultPrimeForm_apply]
  change ((1 / 2 : ℂ) • ((Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form.1 : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 1)) +
    (dolbeaultPrimeCharacter p q)⁻¹ • Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction (dolbeaultIUnit⁻¹)
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form.1 : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 1)))).inChart e y = _
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add,
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul]
  simp only [Pi.smul_apply, Pi.add_apply, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction_inChart _ _ e he hy,
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart form.1 e he hy, inv_inv, dolbeaultIUnit_coe]
  rfl

end

end OAI.AlgebraicTopology.DeRham.Comparison.DolbeaultProjection
