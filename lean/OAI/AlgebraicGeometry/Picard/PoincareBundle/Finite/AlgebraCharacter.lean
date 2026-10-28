import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # Algebra Character -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.AlgebraCharacter

noncomputable section

/-! A nonzero finite commutative algebra over an algebraically closed field has an actual field-valued character. -/

universe u v

variable (k : Type u) [Field k] [IsAlgClosed k]
  (R : Type v) [CommRing R] [Nontrivial R] [Algebra k R] [Module.Finite k R]

/-- A maximal residue field and algebraic closedness construct a character, allowing arbitrary nilpotents in the algebra. -/
theorem exists_character : Nonempty (R →ₐ[k] k) := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal R
  let : I.IsMaximal := hI
  let : Field (R ⧸ I) := Ideal.Quotient.field I
  have : Module.Finite k (R ⧸ I) := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ k I).toLinearMap (Ideal.Quotient.mkₐ_surjective k I)
  let q : (R ⧸ I) →ₐ[k] k := IsAlgClosed.lift
  exact ⟨q.comp (Ideal.Quotient.mkₐ k I)⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Finite.AlgebraCharacter
