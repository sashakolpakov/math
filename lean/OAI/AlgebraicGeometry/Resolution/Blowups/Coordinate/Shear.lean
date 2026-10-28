import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Shear -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.Shear.Construction

noncomputable section

/-! An explicit coordinate shear fixing a chosen hypersurface coordinate. -/

open _root_.MvPolynomial

variable {σ k : Type*} [CommRing k] [DecidableEq σ]

def coordinateShearMap (i j : σ) (c : k) : MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval (fun a => if a = j then X j + C c * X i else X a)

theorem coordinateShearMap_X (i j : σ) (c : k) (a : σ) :
    coordinateShearMap i j c (X a) = if a = j then X j + C c * X i else X a :=
  MvPolynomial.aeval_X _ _

theorem coordinateShearMap_C (i j : σ) (c r : k) :
    coordinateShearMap i j c (C r) = C r := (coordinateShearMap i j c).commutes r

theorem coordinateShearMap_comp (i j : σ) (hij : i ≠ j) (c d : k) :
    (coordinateShearMap i j c).comp (coordinateShearMap i j d) =
      coordinateShearMap i j (c + d) := by
  apply MvPolynomial.algHom_ext
  intro a
  rw [AlgHom.comp_apply, coordinateShearMap_X, coordinateShearMap_X]
  by_cases haj : a = j
  · subst a
    simp [coordinateShearMap_X, hij]
    ring
  · rw [ite_eq_right haj, ite_eq_right haj, coordinateShearMap_X, ite_eq_right haj]

theorem coordinateShearMap_zero (i j : σ) :
    coordinateShearMap (k := k) i j 0 = AlgHom.id k (MvPolynomial σ k) := by
  apply MvPolynomial.algHom_ext
  intro a
  simp [coordinateShearMap_X]
  intro h
  rw [h]

/-- Subtract the fixed coordinate `i` from one complementary coordinate `j`.
Its inverse adds `i` back, so this is a global polynomial algebra automorphism. -/
def coordinateShear (i j : σ) (hij : i ≠ j) : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k :=
  AlgEquiv.ofAlgHom (coordinateShearMap i j (-1 : k)) (coordinateShearMap i j (1 : k))
    (by rw [coordinateShearMap_comp i j hij, neg_add_cancel, coordinateShearMap_zero])
    (by rw [coordinateShearMap_comp i j hij, add_neg_cancel, coordinateShearMap_zero])

theorem coordinateShear_X (i j : σ) (hij : i ≠ j) (a : σ) :
    coordinateShear (k := k) i j hij (X a) = if a = j then X j - X i else X a := by
  change coordinateShearMap i j (-1 : k) (X a) = _
  rw [coordinateShearMap_X]
  simp only [map_neg, map_one, neg_mul, one_mul, sub_eq_add_neg]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.Shear.Construction
