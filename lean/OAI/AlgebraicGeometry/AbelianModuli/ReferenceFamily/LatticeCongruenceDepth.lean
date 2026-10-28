import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeDenominators
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MatrixToLatticeCongruence

/-! # Lattice Congruence Depth -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeCongruenceDepth

noncomputable section

/-! The original full integral lattice supplies its own fixed matrix
congruence depth. Coordinate and basis denominator conditions are proved
from finite generation and rational spanning, rather than added as data.
-/

variable {E : Type*} [Field E] [NumberField E]

theorem exists_lattice_depth_for_integral_matrix_congruence
    (Λ : Submodule ℤ (Fin 3 → E))
    (hO : ∀ a : NumberField.RingOfIntegers E, ∀ x ∈ Λ, (a : E) • x ∈ Λ)
    (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set (Fin 3 → E)) = ⊤)
    (N : ℕ) (hN : 0 < N) :
    ∃ ℓ : ℕ, 0 < ℓ ∧ N ∣ ℓ ∧
      ∀ (D : ℕ) (f : (Fin 3 → E) →ₗ[E] (Fin 3 → E))
        (A : Matrix (Fin 3) (Fin 3) (NumberField.RingOfIntegers E)),
        (∀ i j, (D : E) * (LinearMap.toMatrix' f i j -
          (1 : Matrix (Fin 3) (Fin 3) E) i j) = (ℓ : E) * (A i j : E)) →
        ∀ x ∈ Λ, ∃ y ∈ Λ, (D : E) • (f x - x) = (N : E) • y := by
  obtain ⟨d, hd, hbasis⟩ := LatticeDenominators.common_integer_multiple_mem Λ hspan
    (fun j : Fin 3 => Pi.single j (1 : E))
  obtain ⟨c, hc, hcoords⟩ := LatticeDenominators.common_integral_coordinate_multiple Λ hfg
  let ℓ : ℕ := N * (d * c).natAbs ^ 2
  have hℓ : 0 < ℓ :=
    Nat.mul_pos hN (pow_pos (Int.natAbs_pos.mpr (mul_ne_zero hd hc)) 2)
  have hlevel : (ℓ : ℤ) = (N : ℤ) * d * c * (d * c) := by
    dsimp only [ℓ]
    simp only [Nat.cast_mul, Nat.cast_pow, Int.natCast_natAbs, sq_abs]
    ring
  refine ⟨ℓ, hℓ, ⟨(d * c).natAbs ^ 2, rfl⟩, ?_⟩
  intro D f A hA
  exact MatrixToLatticeCongruence.integral_matrix_congruence_on_lattice Λ hO d c hbasis hcoords
    D ℓ N (d * c) hlevel f A hA

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeCongruenceDepth
