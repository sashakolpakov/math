import OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialRegularSequence
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Polynomial Shifted Regular Sequence -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialShiftedRegularSequence.Constructions

noncomputable section

/-! Polynomial coordinates minus prescribed scalar values form a
regular sequence. Translation is an actual polynomial automorphism,
and flat base change transports the resulting sequence. -/

open RingTheory.Sequence _root_.MvPolynomial

universe u v
variable (R : Type u) [CommRing R] {σ : Type v} (c : σ → R)

def translation : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (aeval (fun i => X i - C (c i))) (aeval (fun i => X i + C (c i)))
    (by ext i; simp) (by ext i; simp)

theorem translation_X (i : σ) : translation R c (X i) = X i - C (c i) := by
  exact aeval_X _ _

theorem shifted_weaklyRegular (ls : List σ) (hl : ls.Nodup) :
    IsWeaklyRegular (MvPolynomial σ R) (ls.map (fun i => X i - C (c i))) := by
  apply ((translation R c).toAddEquiv.isWeaklyRegular_congr
    (as := ls.map (X (R := R))) (bs := ls.map (fun i => X i - C (c i))) ?_).mp
      (PolynomialRegularSequence.Constructions.variables_weaklyRegular ls hl)
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro i _ x
  change translation R c (X i * x) = (X i - C (c i)) * translation R c x
  rw [map_mul, translation_X]

def reflection : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (aeval (fun i => C (c i) - X i)) (aeval (fun i => C (c i) - X i))
    (by ext i; simp) (by ext i; simp)

theorem reflection_X (i : σ) : reflection R c (X i) = C (c i) - X i := by
  exact aeval_X _ _

theorem reflected_weaklyRegular (ls : List σ) (hl : ls.Nodup) :
    IsWeaklyRegular (MvPolynomial σ R) (ls.map (fun i => C (c i) - X i)) := by
  apply ((reflection R c).toAddEquiv.isWeaklyRegular_congr
    (as := ls.map (X (R := R))) (bs := ls.map (fun i => C (c i) - X i)) ?_).mp
      (PolynomialRegularSequence.Constructions.variables_weaklyRegular ls hl)
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro i _ x
  change reflection R c (X i * x) = (C (c i) - X i) * reflection R c x
  rw [map_mul, reflection_X]

variable (A : Type*) [CommRing A] [Algebra (MvPolynomial σ R) A]
  [Module.Flat (MvPolynomial σ R) A]

theorem shifted_flat_weaklyRegular (ls : List σ) (hl : ls.Nodup) :
    IsWeaklyRegular A
      (ls.map (fun i => algebraMap (MvPolynomial σ R) A (X i - C (c i)))) := by
  simpa only [List.map_map, Function.comp_def] using
    (shifted_weaklyRegular R c ls hl).of_flat (S := A)

theorem reflected_flat_weaklyRegular (ls : List σ) (hl : ls.Nodup) :
    IsWeaklyRegular A
      (ls.map (fun i => algebraMap (MvPolynomial σ R) A (C (c i) - X i))) := by
  simpa only [List.map_map, Function.comp_def] using
    (reflected_weaklyRegular R c ls hl).of_flat (S := A)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialShiftedRegularSequence.Constructions
