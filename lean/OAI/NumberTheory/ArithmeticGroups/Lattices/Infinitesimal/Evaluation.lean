import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.TangentExtension
import OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixDerivation

/-! # Evaluation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Evaluation.Construction

noncomputable section

/-! Infinitesimal invariance of a coordinate polynomial survives every
field extension and kills its derivative along extension-field points. -/

open scoped Classical

attribute [local instance] LieRing.ofAssociativeRing

def pointInfinitesimalFunctional {k : Type} [Field k] {n : ℕ}
    (g : Algebraic.SL n k) (p : Algebraic.CoordinatePolynomial n k) : Matrix (Fin n) (Fin n) k →ₗ[k] k where
  toFun A := Algebraic.evaluateMatrix (RingHom.id k) g (Action.Construction.rightInfinitesimal A p)
  map_add' A B := by
    change Algebraic.evaluateMatrix _ _ (Action.Construction.rightInfinitesimalLinear (A + B) p) = _
    rw [map_add, Derivation.add_apply, map_add]
    rfl
  map_smul' c A := by
    change Algebraic.evaluateMatrix _ _ (Action.Construction.rightInfinitesimalLinear (c • A) p) = _
    rw [map_smul, Derivation.smul_apply]
    change Algebraic.evaluateMatrix _ _ (c • Action.Construction.rightInfinitesimal A p) = _
    simp [MvPolynomial.smul_eq_C_mul, Algebraic.evaluateMatrix]

theorem infinitesimal_invariant_evaluate_baseChange
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (p : Algebraic.CoordinatePolynomial n k)
    (hp : ∀ A ∈ Action.Construction.infinitesimalStabilizer G, Action.Construction.rightInfinitesimal A p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G)
    (g : (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)).RationalPoints)
    {A : Matrix (Fin n) (Fin n) K}
    (hA : A ∈ Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K))) :
    Algebraic.evaluateMatrix (RingHom.id K) g.val
      (Action.Construction.rightInfinitesimal A (MvPolynomial.map (algebraMap k K) p)) = 0 := by
  let f := pointInfinitesimalFunctional g.val (MvPolynomial.map (algebraMap k K) p)
  have hle : (Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K))).toSubmodule ≤
      f.ker := by
    rw [TangentExtension.Construction.infinitesimalStabilizer_eq_span_base G hG]
    apply Submodule.span_le.mpr
    rintro _ ⟨B, hB, rfl⟩
    change Algebraic.evaluateMatrix (RingHom.id K) g.val
      (Action.Construction.rightInfinitesimal (B.map (algebraMap k K)) (MvPolynomial.map (algebraMap k K) p)) = 0
    rw [CoefficientMap.Construction.rightInfinitesimal_coefficient_map, BaseChange.Construction.evaluateMatrix_coefficient_map, RingHom.id_comp]
    have hg : g.val ∈ G.subgroup K (algebraMap k K) := by
      have hh := g.property
      change g.val ∈ G.subgroup K ((RingHom.id K).comp (algebraMap k K)) at hh
      simpa only [RingHom.id_comp] using hh
    exact hp B hB K (algebraMap k K) ⟨g.val, hg⟩
  exact hle hA

theorem infinitesimal_invariant_derivation_zero
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (p : Algebraic.CoordinatePolynomial n k)
    (hp : ∀ A ∈ Action.Construction.infinitesimalStabilizer G, Action.Construction.rightInfinitesimal A p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G)
    (g : (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)).RationalPoints) (D : Derivation k K K) :
    D (Algebraic.evaluateMatrix (algebraMap k K) g.val p) = 0 := by
  rw [MatrixDerivation.Construction.derivation_evaluate_matrix D g.val _ (MatrixDerivation.Construction.mul_logarithmicMatrixDerivative D g.val)]
  exact infinitesimal_invariant_evaluate_baseChange G hG p hp g
    (MatrixDerivation.Construction.logarithmicMatrixDerivative_mem G hG D g)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Evaluation.Construction
