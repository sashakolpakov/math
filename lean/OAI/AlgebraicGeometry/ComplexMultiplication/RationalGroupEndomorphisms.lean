import OAI.AlgebraicGeometry.ComplexMultiplication.GroupEndomorphismRing
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Rat

/-! # Rational Group Endomorphisms -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.RationalGroupEndomorphisms

noncomputable section

/-! # Rational algebraic group endomorphisms

For a commutative group scheme, this is the actual endomorphism ring tensored with ℚ.
No cohomological model replaces its group-scheme morphisms.
-/

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] [BraidedCategory C]
  (X : C) [GrpObj X] [IsCommMonObj X]

/-- The usual rationalization `End⁰(X) = ℚ ⊗[ℤ] End(X)`. -/
def RationalGroupEndomorphism := ℚ ⊗[ℤ] GroupEndomorphismRing.GroupEndomorphism X

instance CMRationalGroupEndomorphisms.localInstance1 : _root_.Ring (RationalGroupEndomorphism X) :=
  inferInstanceAs (_root_.Ring (ℚ ⊗[ℤ] GroupEndomorphismRing.GroupEndomorphism X))

instance CMRationalGroupEndomorphisms.localInstance2 : Algebra ℚ (RationalGroupEndomorphism X) :=
  inferInstanceAs (Algebra ℚ (ℚ ⊗[ℤ] GroupEndomorphismRing.GroupEndomorphism X))

/-- Inclusion of genuine integral group endomorphisms into their rationalization. -/
def groupEndomorphismRationalization :
    GroupEndomorphismRing.GroupEndomorphism X →ₐ[ℤ] RationalGroupEndomorphism X :=
  Algebra.TensorProduct.includeRight

end

end OAI.AlgebraicGeometry.ComplexMultiplication.RationalGroupEndomorphisms
