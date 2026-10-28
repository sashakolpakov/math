import OAI.NumberTheory.ArithmeticGroups.Lattices.CongruencePolynomial
import OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.InfinitesimalExtension
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.PolynomialConstants

/-! # Invariant Integration -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.InvariantIntegration.Construction

noncomputable section

/-! On a geometrically connected characteristic-zero group, an
infinitesimally invariant bilinear form is invariant over every field
extension. -/

open scoped Classical
open _root_.Matrix

attribute [local instance] LieRing.ofAssociativeRing

theorem congruencePolynomial_infinitesimal_vanishing
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (Q : Matrix (Fin n) (Fin n) k)
    (hQ : ∀ A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G, A.transpose * Q + Q * A = 0)
    (i j : Fin n) :
    ∀ A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G,
      Infinitesimal.Action.Construction.rightInfinitesimal A (CongruencePolynomial.Construction.congruencePolynomial Q i j) ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G := by
  intro A hA K _ v g
  let : Algebra k K := v.toAlgebra
  let H := BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)
  let gH : H.RationalPoints := ⟨g.val, by
    change g.val ∈ G.subgroup K ((RingHom.id K).comp v)
    rw [RingHom.id_comp]
    exact g.property⟩
  have hQK := InfinitesimalExtension.Construction.bilinear_infinitesimal_invariant_baseChange (K := K) G hG Q hQ
  have hz := InfinitesimalExtension.Construction.bilinear_infinitesimal_invariant_derivative_zero H (Q.map (algebraMap k K)) hQK gH
    (CharZeroTangent.Construction.infinitesimalStabilizer_coefficient_map G hG hA)
  rw [CongruencePolynomial.Construction.derivative_congruencePolynomial_evaluate]
  exact congrArg (fun M => M i j) hz

theorem bilinear_form_invariant_of_infinitesimal
    {k K : Type} [Field k] [CharZero k] [Field K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (Q : Matrix (Fin n) (Fin n) k)
    (hQ : ∀ A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G, A.transpose * Q + Q * A = 0)
    (v : k →+* K) (g : G.Points v) :
    (g.val : Matrix (Fin n) (Fin n) K).transpose * Q.map v *
      (g.val : Matrix (Fin n) (Fin n) K) = Q.map v := by
  ext i j
  have he := Infinitesimal.PolynomialConstants.Construction.evaluate_infinitesimal_invariant_constant G hG (CongruencePolynomial.Construction.congruencePolynomial Q i j)
    (congruencePolynomial_infinitesimal_vanishing G hG Q hQ i j) v g
  rw [CongruencePolynomial.Construction.evaluate_congruencePolynomial, CongruencePolynomial.Construction.evaluate_congruencePolynomial] at he
  simpa only [Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.one_mul,
    Matrix.mul_one, Matrix.map_id, Matrix.map_apply, RingHom.id_apply] using he

theorem compact_real_place_positive_invariant_form
    {k : Type} [Field k] [CharZero k] (G : Algebraic.ConnectedSemisimpleKGroup k)
    (v : k →+* ℝ) (hv : Algebraic.IsCompactAtRealPlace G v) :
    ∃ Q : Matrix (Fin G.dimension) (Fin G.dimension) k,
      (∀ x : Fin G.dimension → ℝ, x ≠ 0 → 0 < dotProduct x ((Q.map v).mulVec x)) ∧
      ∀ (K : Type) [Field K] (ι : k →+* K) (g : G.matrixGroup.Points ι),
        (g.val : Matrix (Fin G.dimension) (Fin G.dimension) K).transpose * Q.map ι *
          (g.val : Matrix (Fin G.dimension) (Fin G.dimension) K) = Q.map ι := by
  obtain ⟨Q, hQ, hpos⟩ := Compact.RationalForm.Construction.compact_real_place_positive_infinitesimal_form G v hv
  exact ⟨Q, hpos, fun K _ ι g => bilinear_form_invariant_of_infinitesimal
    G.matrixGroup G.connected Q hQ ι g⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.InvariantIntegration.Construction
