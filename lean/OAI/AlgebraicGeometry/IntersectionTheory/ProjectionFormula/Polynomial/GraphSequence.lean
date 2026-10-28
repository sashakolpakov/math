import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.RegularSequence
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Graph Sequence -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.GraphSequence

noncomputable section

/-! Equations Xᵢ - aᵢ of a polynomial graph form a weakly regular
sequence. Translation is an explicit polynomial algebra automorphism. -/

universe u v

open _root_.MvPolynomial RingTheory.Sequence

variable (R : Type u) [CommRing R] (σ : Type v)

def translation (a : σ → R) : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (aeval fun i => X i - C (a i)) (aeval fun i => X i + C (a i))
    (by ext i; simp) (by ext i; simp)

theorem translation_X (a : σ → R) (i : σ) :
    translation R σ a (X i) = X i - C (a i) := by simp [translation]

theorem weakly_regular (a : σ → R) (xs : List σ) (hx : xs.Nodup) :
    IsWeaklyRegular (MvPolynomial σ R) (xs.map fun i => X i - C (a i)) := by
  have hc : IsWeaklyRegular (MvPolynomial σ R) (xs.map (X : σ → MvPolynomial σ R)) ↔
      IsWeaklyRegular (MvPolynomial σ R) (xs.map fun i => X i - C (a i)) := by
    apply AddEquiv.isWeaklyRegular_congr (e := (translation R σ a).toRingEquiv.toAddEquiv)
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro i _ x
    change translation R σ a (X i * x) = (X i - C (a i)) * translation R σ a x
    rw [map_mul, translation_X]
  exact hc.mp (RegularSequence.weakly_regular R σ xs hx)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.GraphSequence
