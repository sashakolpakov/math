import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CechHomotopy
import Mathlib.Data.Int.Interval

/-! # Negative Degree -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.NegativeDegree.ProjectiveCech

noncomputable section

/-! In each fixed degree, only finitely many Laurent monomials have every coordinate exponent negative. -/

universe u

variable {σ : Type u} [Fintype σ]

abbrev NegativeDegreeExponents (d : ℤ) := {a : σ → ℤ // LaurentDegree.ProjectiveCech.exponentDegree a = d ∧ ∀ i, a i < 0}

theorem negativeDegreeExponent_bounds {d : ℤ} (a : NegativeDegreeExponents (σ := σ) d) (i : σ) :
    d ≤ a.val i ∧ a.val i ≤ 0 := by
  classical
  refine ⟨?_, (a.property.2 i).le⟩
  have h : -a.val i ≤ ∑ j, -a.val j :=
    Finset.single_le_sum (fun j _ => neg_nonneg.mpr (a.property.2 j).le) (Finset.mem_univ i)
  rw [Finset.sum_neg_distrib] at h
  change -a.val i ≤ -LaurentDegree.ProjectiveCech.exponentDegree a.val at h
  have hd := a.property.1
  omega

def negativeDegreeExponentEmbedding (d : ℤ) :
    NegativeDegreeExponents (σ := σ) d ↪ (σ → Set.Icc d 0) where
  toFun a i := ⟨a.val i, negativeDegreeExponent_bounds a i⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)

instance negativeDegreeExponents_finite (d : ℤ) : Finite (NegativeDegreeExponents (σ := σ) d) :=
  Finite.of_injective (negativeDegreeExponentEmbedding (σ := σ) d)
    (negativeDegreeExponentEmbedding (σ := σ) d).injective

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.NegativeDegree.ProjectiveCech
