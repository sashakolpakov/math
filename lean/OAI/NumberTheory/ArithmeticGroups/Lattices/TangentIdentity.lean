import OAI.NumberTheory.ArithmeticGroups.Lattices.LeftTranslation
import OAI.NumberTheory.ArithmeticGroups.Lattices.BaseChange
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Trace

/-! # Tangent Identity -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.TangentIdentity.Construction

noncomputable section

/-! Over an algebraically closed field, infinitesimal ideal preservation
is equivalent to the tangent equations at the identity. -/

open scoped Classical

theorem leftTranslate_evaluate_one {k : Type} [Field k] {n : ℕ}
    (g : Algebraic.SL n k) (p : Algebraic.CoordinatePolynomial n k) :
    Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (LeftTranslation.Construction.leftTranslate (g : Matrix (Fin n) (Fin n) k) p) =
      Algebraic.evaluateMatrix (RingHom.id k) g p := by
  have hg : Matrix.SpecialLinearGroup.map (RingHom.id k) g = g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rfl
  rw [LeftTranslation.Construction.leftTranslate_evaluate, hg, mul_one]

theorem mem_infinitesimalStabilizer_iff_at_identity
    {k : Type} [Field k] [IsAlgClosed k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (A : Matrix (Fin n) (Fin n) k) :
    A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G ↔
      ∀ p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G,
        Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (Infinitesimal.Action.Construction.rightInfinitesimal A p) = 0 := by
  constructor
  · intro hA p hp
    exact (Infinitesimal.Action.Construction.mem_infinitesimalStabilizer G A).mp hA p hp k (RingHom.id k)
      (1 : G.RationalPoints)
  · intro ht
    apply (Infinitesimal.Action.Construction.mem_infinitesimalStabilizer G A).mpr
    intro p hp
    apply (BaseChange.Construction.mem_vanishingIdeal_iff_rational_of_algClosed G _).mpr
    intro g
    have h := ht (LeftTranslation.Construction.leftTranslate (g.val : Matrix (Fin n) (Fin n) k) p)
      (LeftTranslation.Construction.leftTranslate_mem_vanishingIdeal G g.val g.property p hp)
    rw [LeftTranslation.Construction.rightInfinitesimal_leftTranslate, leftTranslate_evaluate_one] at h
    exact h

theorem tangent_equations_trace_zero
    {k : Type} [Field k] [IsAlgClosed k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (A : Matrix (Fin n) (Fin n) k)
    (hA : ∀ p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G,
      Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (Infinitesimal.Action.Construction.rightInfinitesimal A p) = 0) :
    A.trace = 0 :=
  Infinitesimal.Trace.Construction.infinitesimalStabilizer_trace_zero G ((mem_infinitesimalStabilizer_iff_at_identity G A).mpr hA)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.TangentIdentity.Construction
