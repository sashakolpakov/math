import OAI.NumberTheory.ArithmeticGroups.Lattices.VanishingIdeal

/-! # Action -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Action.Construction

noncomputable section

section

/-! The infinitesimal right action of matrices on the coordinate
polynomial algebra. -/

open scoped Classical
open _root_.MvPolynomial

variable {k : Type} [Field k] {n : ℕ}

attribute [local instance] LieRing.ofAssociativeRing

def rightInfinitesimal (A : Matrix (Fin n) (Fin n) k) :
    Derivation k (Algebraic.CoordinatePolynomial n k) (Algebraic.CoordinatePolynomial n k) :=
  MvPolynomial.mkDerivation k (fun ij => ∑ l, X (ij.1, l) * C (A l ij.2))

@[simp] theorem rightInfinitesimal_X (A : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    rightInfinitesimal A (X (i, j)) = ∑ l, X (i, l) * C (A l j) :=
  MvPolynomial.mkDerivation_X k _ (i, j)

@[simp] theorem rightInfinitesimal_C (A : Matrix (Fin n) (Fin n) k) (c : k) :
    rightInfinitesimal A (C c) = 0 :=
  (rightInfinitesimal A).map_algebraMap c

theorem rightInfinitesimal_mul_C (A : Matrix (Fin n) (Fin n) k)
    (p : Algebraic.CoordinatePolynomial n k) (c : k) :
    rightInfinitesimal A (p * C c) = rightInfinitesimal A p * C c := by
  rw [Derivation.leibniz, rightInfinitesimal_C, smul_zero, zero_add, smul_eq_mul, mul_comm]

theorem rightInfinitesimal_on_linear_entry (A B : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    rightInfinitesimal A (∑ l, X (i, l) * C (B l j)) =
      ∑ l, X (i, l) * C ((A * B) l j) := by
  simp only [map_sum, rightInfinitesimal_mul_C, rightInfinitesimal_X, Matrix.mul_apply,
    map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem rightInfinitesimal_bracket (A B : Matrix (Fin n) (Fin n) k) :
    rightInfinitesimal ⁅A, B⁆ = ⁅rightInfinitesimal A, rightInfinitesimal B⁆ := by
  apply MvPolynomial.derivation_ext
  rintro ⟨i, j⟩
  rw [Derivation.commutator_apply, rightInfinitesimal_X, rightInfinitesimal_X,
    rightInfinitesimal_X, rightInfinitesimal_on_linear_entry, rightInfinitesimal_on_linear_entry]
  simp only [Ring.lie_def, Matrix.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

def rightInfinitesimalLinear :
    Matrix (Fin n) (Fin n) k →ₗ[k]
      Derivation k (Algebraic.CoordinatePolynomial n k) (Algebraic.CoordinatePolynomial n k) where
  toFun := rightInfinitesimal
  map_add' A B := by
    apply MvPolynomial.derivation_ext
    rintro ⟨i, j⟩
    simp only [Derivation.add_apply, rightInfinitesimal_X, Matrix.add_apply,
      map_add, mul_add, Finset.sum_add_distrib]
  map_smul' c A := by
    apply MvPolynomial.derivation_ext
    rintro ⟨i, j⟩
    simp only [Derivation.smul_apply, rightInfinitesimal_X, Matrix.smul_apply,
      smul_eq_mul, map_mul, Finset.smul_sum, MvPolynomial.smul_eq_C_mul, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro l _
    ring

def rightInfinitesimalLie :
    Matrix (Fin n) (Fin n) k →ₗ⁅k⁆
      Derivation k (Algebraic.CoordinatePolynomial n k) (Algebraic.CoordinatePolynomial n k) where
  toLinearMap := rightInfinitesimalLinear
  map_lie' := fun {A B} => rightInfinitesimal_bracket A B

end

section

/-! The Lie algebra of polynomial derivations preserving the matrix
group's universal vanishing ideal. -/

open scoped Classical
open _root_.MvPolynomial

attribute [local instance] LieRing.ofAssociativeRing

def idealPreservingDerivations {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    (I : Ideal A) : LieSubalgebra k (Derivation k A A) where
  carrier := {D | ∀ p ∈ I, D p ∈ I}
  zero_mem' := by intro p _; exact I.zero_mem
  add_mem' := by
    intro D E hD hE p hp
    exact I.add_mem (hD p hp) (hE p hp)
  smul_mem' := by
    intro c D hD p hp
    exact (I.restrictScalars k).smul_mem c (hD p hp)
  lie_mem' := by
    intro D E hD hE p hp
    exact I.sub_mem (hD _ (hE p hp)) (hE _ (hD p hp))

def infinitesimalStabilizer {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) : LieSubalgebra k (Matrix (Fin n) (Fin n) k) :=
  (idealPreservingDerivations (VanishingIdeal.Construction.coordinateVanishingIdeal G)).comap rightInfinitesimalLie

theorem mem_infinitesimalStabilizer {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (A : Matrix (Fin n) (Fin n) k) :
    A ∈ infinitesimalStabilizer G ↔
      ∀ p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G, rightInfinitesimal A p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G := Iff.rfl

theorem evaluate_rightInfinitesimal_X {k : Type} [Field k] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (rightInfinitesimal A (X (i, j))) = A i j := by
  rw [rightInfinitesimal_X]
  simp [Algebraic.evaluateMatrix, Matrix.one_apply]

theorem rightInfinitesimal_injective {k : Type} [Field k] {n : ℕ} :
    Function.Injective (rightInfinitesimal : Matrix (Fin n) (Fin n) k → _) := by
  intro A B h
  ext i j
  have he := congrArg
    (fun D : Derivation k (Algebraic.CoordinatePolynomial n k) (Algebraic.CoordinatePolynomial n k) =>
      Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (D (X (i, j)))) h
  simpa only [evaluate_rightInfinitesimal_X] using he

end

/-! Conjugation by rational group points preserves the infinitesimal
stabilizer of the universal vanishing ideal. -/

open scoped Classical
open _root_.MvPolynomial

def conjugatePolynomialDerivation {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    (e : A ≃ₐ[k] A) (D : Derivation k A A) : Derivation k A A where
  toLinearMap := e.toLinearMap.comp (D.toLinearMap.comp e.symm.toLinearMap)
  map_one_eq_zero' := by simp
  leibniz' p q := by simp [Derivation.leibniz, smul_eq_mul]

theorem conjugatePolynomialDerivation_apply {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    (e : A ≃ₐ[k] A) (D : Derivation k A A) (p : A) :
    conjugatePolynomialDerivation e D p = e (D (e.symm p)) := rfl

theorem rightTranslate_on_linear_entry {k : Type} [Field k] {n : ℕ}
    (g A : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    PolynomialAction.Construction.rightTranslate g (∑ l, X (i, l) * C (A l j)) =
      ∑ l, X (i, l) * C ((g * A) l j) := by
  have h := congrArg (fun f : Algebraic.CoordinatePolynomial n k →ₐ[k] Algebraic.CoordinatePolynomial n k =>
    f (X (i, j))) (PolynomialAction.Construction.rightTranslate_mul g A)
  simpa only [AlgHom.comp_apply, PolynomialAction.Construction.rightTranslate_X] using h.symm

theorem rightInfinitesimal_conjugation {k : Type} [Field k] {n : ℕ}
    (g : Algebraic.SL n k) (A : Matrix (Fin n) (Fin n) k) :
    rightInfinitesimal ((g : Matrix (Fin n) (Fin n) k) * A *
      ((g⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k)) =
      conjugatePolynomialDerivation (PolynomialAction.Construction.rightTranslateEquiv g) (rightInfinitesimal A) := by
  apply MvPolynomial.derivation_ext
  rintro ⟨i, j⟩
  rw [conjugatePolynomialDerivation_apply]
  change rightInfinitesimal ((g : Matrix (Fin n) (Fin n) k) * A *
    ((g⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k)) (X (i, j)) =
    PolynomialAction.Construction.rightTranslate (g : Matrix (Fin n) (Fin n) k)
      (rightInfinitesimal A (PolynomialAction.Construction.rightTranslate ((g⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) (X (i, j))))
  rw [rightInfinitesimal_X, PolynomialAction.Construction.rightTranslate_X, rightInfinitesimal_on_linear_entry,
    rightTranslate_on_linear_entry, Matrix.mul_assoc]

theorem infinitesimalStabilizer_conjugation {k : Type} [Field k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (g : G.RationalPoints)
    {A : Matrix (Fin n) (Fin n) k} (hA : A ∈ infinitesimalStabilizer G) :
    ((g.val : Matrix (Fin n) (Fin n) k) * A *
      ((g.val⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k)) ∈ infinitesimalStabilizer G := by
  apply (mem_infinitesimalStabilizer G _).mpr
  intro p hp
  rw [rightInfinitesimal_conjugation, conjugatePolynomialDerivation_apply]
  apply VanishingIdeal.Construction.rightTranslate_mem_vanishingIdeal G g.val g.property
  apply (mem_infinitesimalStabilizer G A).mp hA
  exact VanishingIdeal.Construction.rightTranslate_mem_vanishingIdeal G g.val⁻¹
    ((G.subgroup k (RingHom.id k)).inv_mem g.property) p hp

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Action.Construction
