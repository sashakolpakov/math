import OAI.AlgebraicGeometry.PELModuli.CMPoints.LatticeQuotients
import OAI.AlgebraicGeometry.PELModuli.CMPoints.CoordinateBlocks
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Arithmetic

/-! # Lattice Blocks -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.LatticeBlocks

noncomputable section

/-! The actual split coefficient coordinates compute every projector
block of a rank-three lattice quotient: its cardinality is q^(3*n). -/

open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)

def splitCoefficientEquiv (n : ℕ) :
    (NumberField.RingOfIntegers E ⧸ Ideal.span ({(q ^ n : NumberField.RingOfIntegers E)} :
      Set (NumberField.RingOfIntegers E))) ≃+* (Gal(E/ℚ) → ZMod (q ^ n)) :=
  (Ideal.quotEquivOfEq (hsplit n).2.symm).trans
    ((j.residueCoordinates iota n).quotientKerEquivOfSurjective (hsplit n).1)

theorem splitCoefficientEquiv_projector (n : ℕ) (τ : Gal(E/ℚ)) :
    splitCoefficientEquiv j iota hsplit n
      (Ideal.Quotient.mk _ (j.projector iota hsplit n τ)) = Pi.single τ 1 :=
  j.projector_coordinates iota hsplit n τ

theorem projector_card_of_coordinates {V : Type*} [AddCommGroup V]
    [Module (NumberField.RingOfIntegers E) V] (n : ℕ)
    (e : V
      ≃ₗ[NumberField.RingOfIntegers E]
        (Fin 3 → NumberField.RingOfIntegers E ⧸
          Ideal.span ({(q ^ n : NumberField.RingOfIntegers E)} : Set (NumberField.RingOfIntegers E))))
    (τ : Gal(E/ℚ)) :
    Nat.card {x : V //
      (j.projector iota hsplit n τ) • x = x} = q ^ (3 * n) := by
  let e₁ := CoordinateBlocks.scalarFixedEquiv e (j.projector iota hsplit n τ)
  let e₂ := CoordinateBlocks.quotientCoordinateBlockEquiv (I := Fin 3)
    (Ideal.span ({(q ^ n : NumberField.RingOfIntegers E)} : Set (NumberField.RingOfIntegers E)))
    (splitCoefficientEquiv j iota hsplit n) (j.projector iota hsplit n τ) τ
    (splitCoefficientEquiv_projector j iota hsplit n τ)
  rw [Nat.card_congr (e₁.trans e₂)]
  simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin, ← pow_mul, Nat.mul_comm n 3]

theorem lattice_projector_card
    (Λ : Submodule ℤ (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ) (n : ℕ)
    (e : ScalarQuotientMk.ScalarQuotient (NumberField.RingOfIntegers E) (LatticeComparison.stableIntegerLattice Λ hΛ) (q ^ n)
      ≃ₗ[NumberField.RingOfIntegers E]
        (Fin 3 → NumberField.RingOfIntegers E ⧸
          Ideal.span ({(q ^ n : NumberField.RingOfIntegers E)} : Set (NumberField.RingOfIntegers E))))
    (τ : Gal(E/ℚ)) :
    Nat.card {x : ScalarQuotientMk.ScalarQuotient (NumberField.RingOfIntegers E) (LatticeComparison.stableIntegerLattice Λ hΛ) (q ^ n) //
      (j.projector iota hsplit n τ) • x = x} = q ^ (3 * n) :=
  projector_card_of_coordinates j iota hsplit n e τ

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.LatticeBlocks
