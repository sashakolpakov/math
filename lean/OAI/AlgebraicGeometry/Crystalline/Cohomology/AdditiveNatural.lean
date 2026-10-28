import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Additive Natural -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.AdditiveNatural.AdditiveNaturalScalars

/-! # Additive functors preserve the natural-number scalar action -/

open _root_.CategoryTheory

variable (R S : Type*) [Semiring R] [Semiring S]
  {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [Linear R C] [Linear S D] (G : C ⥤ D) [G.Additive]

theorem map_nat_smul {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    G.map ((n : R) • f) = (n : S) • G.map f := by
  rw [Nat.cast_smul_eq_nsmul R, G.map_nsmul, Nat.cast_smul_eq_nsmul S]

theorem map_nat_pow_smul {X Y : C} (f : X ⟶ Y) (p n : ℕ) :
    G.map ((p : R) ^ n • f) = (p : S) ^ n • G.map f := by
  rw [← Nat.cast_pow, map_nat_smul R S, Nat.cast_pow]

end OAI.AlgebraicGeometry.Crystalline.Cohomology.AdditiveNatural.AdditiveNaturalScalars
