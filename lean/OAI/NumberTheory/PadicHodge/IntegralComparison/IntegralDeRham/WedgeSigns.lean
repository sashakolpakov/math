import OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.WedgeNaturality
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-! # Wedge Signs -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.WedgeSigns

noncomputable section

/-! The integral signs for moving one differential past a block of
differentials follow from the native alternating-symbol relations. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

theorem insertNth_append {A : Type*} (p q : ℕ) (a : A)
    (v : Fin p → A) (w : Fin q → A) :
    (⟨p, by omega⟩ : Fin (p + q + 1)).insertNth a (Fin.append v w) =
      Fin.append v (Fin.cons a w) := by
  funext i
  refine Fin.addCases (m := p) (n := q + 1) (fun j => ?_) (fun j => ?_) i
  · rw [Fin.insertNth_apply_below (by change j.val < p; exact j.isLt)]
    simp only [eq_rec_constant]
    change Fin.append v w (j.castAdd q) = Fin.append v (Fin.cons a w) (j.castAdd (q + 1))
    rw [Fin.append_left, Fin.append_left]
  · refine Fin.cases ?_ (fun j => ?_) j
    · have h : Fin.natAdd p (0 : Fin (q + 1)) = (⟨p, by omega⟩ : Fin (p + q + 1)) :=
        Fin.ext (Nat.add_zero p)
      rw [h, Fin.insertNth_apply_same]
      change a = Fin.append v (Fin.cons a w) (Fin.natAdd p 0)
      simp
    · rw [Fin.insertNth_apply_above (by change p < p + (j.val + 1); omega)]
      simp only [eq_rec_constant]
      change Fin.append v w (Fin.natAdd p j) =
        Fin.append v (Fin.cons a w) (Fin.natAdd p j.succ)
      simp

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

def degreeCast {m n : ℕ} (h : m = n) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A m ≃ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n := by
  subst n
  exact LinearEquiv.refl _ _

theorem degreeCast_symbol {m n : ℕ} (h : m = n) (a : A) (v : Fin m → A) :
    degreeCast R A h (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a (fun i => v (Fin.cast h.symm i)) := by
  subst n
  rfl

theorem symbol_append_cons (p q : ℕ) (b : A) (v : Fin p → A) (w : Fin q → A) :
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 (Fin.append v (Fin.cons b w)) =
      (-1 : ℤ) ^ p • AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 (Fin.cons b (Fin.append v w)) := by
  have h := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbols R A (p + q + 1)).map_insertNth
    (⟨p, by omega⟩ : Fin (p + q + 1)) b (Fin.append v w)
  rw [insertNth_append] at h
  exact h

theorem degreeCast_append_cons (p q : ℕ) (a b : A) (v : Fin p → A) (w : Fin q → A) :
    degreeCast R A (by omega : (p + 1) + q = p + q + 1)
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b (Fin.append (Fin.cons a v) w)) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b (Fin.cons a (Fin.append v w)) := by
  rw [degreeCast_symbol]
  apply congrArg (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b)
  funext i
  rw [Fin.append_cons]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.WedgeSigns
