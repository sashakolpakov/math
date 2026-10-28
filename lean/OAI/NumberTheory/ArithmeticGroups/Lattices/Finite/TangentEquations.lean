import OAI.NumberTheory.ArithmeticGroups.Lattices.CharZeroTangent

/-! # Tangent Equations -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.TangentEquations.Construction

noncomputable section

/-! One finite list of linear tangent equations works over all extension
fields for a geometrically connected characteristic-zero matrix group. -/

open scoped Classical

attribute [local instance] LieRing.ofAssociativeRing

def tangentFunctional {k : Type} [Field k] {n : ℕ}
    (p : Algebraic.CoordinatePolynomial n k) : Matrix (Fin n) (Fin n) k →ₗ[k] k where
  toFun A := Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (Infinitesimal.Action.Construction.rightInfinitesimal A p)
  map_add' A B := by
    change Algebraic.evaluateMatrix _ _ (Infinitesimal.Action.Construction.rightInfinitesimalLinear (A + B) p) = _
    rw [map_add, Derivation.add_apply, map_add]
    rfl
  map_smul' c A := by
    change Algebraic.evaluateMatrix _ _ (Infinitesimal.Action.Construction.rightInfinitesimalLinear (c • A) p) = _
    rw [map_smul, Derivation.smul_apply]
    change Algebraic.evaluateMatrix _ _ (c • Infinitesimal.Action.Construction.rightInfinitesimal A p) = _
    simp [MvPolynomial.smul_eq_C_mul, Algebraic.evaluateMatrix]

def tangentSystem {k ι : Type} [Field k] {n : ℕ}
    (p : ι → Algebraic.CoordinatePolynomial n k) : Matrix (Fin n) (Fin n) k →ₗ[k] (ι → k) :=
  LinearMap.pi (fun i => tangentFunctional (p i))

theorem infinitesimalStabilizer_finite_generators
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (S : Finset (Algebraic.CoordinatePolynomial n k))
    (hS : Ideal.span (S : Set (Algebraic.CoordinatePolynomial n k)) = VanishingIdeal.Construction.coordinateVanishingIdeal G)
    (A : Matrix (Fin n) (Fin n) K) :
    A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)) ↔
      ∀ p ∈ S, tangentFunctional (MvPolynomial.map (algebraMap k K) p) A = 0 := by
  let : CharZero K := Algebra.charZero_of_charZero k K
  rw [CharZeroTangent.Construction.mem_infinitesimalStabilizer_iff_tangent _ (ConnectedBaseChange.Construction.geometrically_connected_baseChange G hG)]
  constructor
  · intro h p hp
    apply h
    apply BaseChange.Construction.coefficient_map_mem_baseChange_vanishingIdeal
    rw [← hS]
    exact Ideal.subset_span hp
  · intro h
    apply (Infinitesimal.CoefficientMap.Construction.vanishingIdeal_le_identityTangentIdeal_iff _ _).mp
    rw [GeneralVanishingBaseChange.Construction.vanishingIdeal_charZero_baseChange G hG, Ideal.map_le_iff_le_comap, ← hS]
    apply Ideal.span_le.mpr
    intro p hp
    refine ⟨?_, h p hp⟩
    rw [Infinitesimal.CoefficientMap.Construction.evaluate_one_coefficient_map]
    have hpI : p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G := hS ▸ Ideal.subset_span hp
    have hp0 : Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) p = 0 :=
      hpI k (RingHom.id k) (1 : G.RationalPoints)
    rw [hp0, map_zero]

theorem exists_uniform_finite_tangent_system
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → Algebraic.CoordinatePolynomial n k),
      ∀ (K : Type) [Field K] [Algebra k K],
        (Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K))).toSubmodule =
          (tangentSystem (fun i => MvPolynomial.map (algebraMap k K) (p i))).ker := by
  obtain ⟨S, hS⟩ := VanishingIdeal.Construction.vanishingIdeal_finitely_generated G
  refine ⟨S, inferInstance, Subtype.val, fun K _ _ => ?_⟩
  ext A
  rw [LieSubalgebra.mem_toSubmodule, infinitesimalStabilizer_finite_generators G hG S hS]
  change (∀ p ∈ S, tangentFunctional (MvPolynomial.map (algebraMap k K) p) A = 0) ↔
    (fun p : S => tangentFunctional (MvPolynomial.map (algebraMap k K) p.val) A) = 0
  constructor
  · intro h
    funext p
    exact h p.val p.property
  · intro h p hp
    exact congrFun h ⟨p, hp⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.TangentEquations.Construction
