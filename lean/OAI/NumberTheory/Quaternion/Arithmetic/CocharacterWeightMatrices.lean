import OAI.NumberTheory.Quaternion.Arithmetic.LaurentEvaluation
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.Place
import OAI.NumberTheory.Quaternion.Arithmetic.PolynomialGaloisNorm

/-! # Cocharacter Weight Matrices -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.CocharacterWeightMatrices

noncomputable section

/-! The Laurent coefficients of a cocharacter's matrix entries are
weight matrices: left multiplication by the cocharacter scales each
weight matrix by the corresponding character. -/

open scoped Classical
open OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.Place.Construction

variable {F : Type} [Field F] [CharZero F] {n : ℕ}
  {G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n}

def cocharacterLaurentMatrix (c : G.Cocharacter) :
    Matrix (Fin n) (Fin n) (LaurentPolynomial F) :=
  fun i j => ArithmeticGroups.Lattices.Laurent.Construction.laurentOfPair (c.coordinates i j)

def cocharacterWeightMatrix (c : G.Cocharacter) (z : ℤ) : Matrix (Fin n) (Fin n) F :=
  fun i j => (cocharacterLaurentMatrix c i j).coeff z

theorem cocharacter_laurent_left_scale (c : G.Cocharacter) (s : Fˣ) (i j : Fin n) :
    LaurentEvaluation.laurentWeightScale s (cocharacterLaurentMatrix c i j) =
      ∑ l, LaurentPolynomial.C ((c.hom F (RingHom.id F) s).val i l) * cocharacterLaurentMatrix c l j := by
  apply LaurentEvaluation.laurent_eq_of_unit_evaluations
  intro t
  calc
    LaurentPolynomial.eval₂ (RingHom.id F) t (LaurentEvaluation.laurentWeightScale s (cocharacterLaurentMatrix c i j)) =
        (c.hom F (RingHom.id F) (s * t)).val i j := by
      rw [LaurentEvaluation.laurentWeightScale_eval]
      exact (ArithmeticGroups.Lattices.Compact.Place.Construction.cocharacter_entry_eq_laurent G c (RingHom.id F) (s * t) i j).symm
    _ = ∑ l, (c.hom F (RingHom.id F) s).val i l * (c.hom F (RingHom.id F) t).val l j := by
      rw [map_mul]
      rfl
    _ = _ := by
      simp only [map_sum, map_mul, LaurentPolynomial.eval₂_C, RingHom.id_apply]
      apply Finset.sum_congr rfl
      intro l _
      rw [ArithmeticGroups.Lattices.Compact.Place.Construction.cocharacter_entry_eq_laurent G c (RingHom.id F) t l j]
      rfl

theorem cocharacter_weight_matrix_action (c : G.Cocharacter) (s : Fˣ) (z : ℤ) :
    (c.hom F (RingHom.id F) s).val.val * cocharacterWeightMatrix c z =
      (s ^ z).val • cocharacterWeightMatrix c z := by
  apply Matrix.ext
  intro i j
  have he := congrArg (fun p : LaurentPolynomial F => p.coeff z) (cocharacter_laurent_left_scale c s i j)
  simp only [LaurentEvaluation.laurentWeightScale_coeff, AddMonoidAlgebra.coeff_sum, Finset.sum_apply',
    LaurentEvaluation.laurent_constant_mul_coeff] at he
  change (∑ l, (c.hom F (RingHom.id F) s).val i l *
    (cocharacterLaurentMatrix c l j).coeff z) = (s ^ z).val * (cocharacterLaurentMatrix c i j).coeff z
  exact he.symm.trans (mul_comm _ _)

end

end OAI.NumberTheory.Quaternion.Arithmetic.CocharacterWeightMatrices
