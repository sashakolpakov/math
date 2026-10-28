import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Evaluation
import OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialConstants
import OAI.NumberTheory.ArithmeticGroups.Lattices.GenericPoint

/-! # Polynomial Constants -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.PolynomialConstants.Construction

noncomputable section

/-! On a geometrically connected characteristic-zero matrix group,
polynomials killed by every infinitesimal right action are constant.
This is proved using the generic point and derivations of its function
field, and the result holds on points over every extension field. -/

open scoped Classical

theorem infinitesimal_invariant_constant_of_algClosed
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (p : Algebraic.CoordinatePolynomial n k)
    (hp : ∀ A ∈ Action.Construction.infinitesimalStabilizer G, Action.Construction.rightInfinitesimal A p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G) :
    p - MvPolynomial.C (Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) p) ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G := by
  let : (VanishingIdeal.Construction.coordinateVanishingIdeal G).IsPrime := GeometricIrreducibility.Construction.coordinateVanishingIdeal_isPrime G hG
  let K := GenericPoint.Construction.MatrixFunctionField G
  let : Algebra k K := (GenericPoint.Construction.genericBaseEmbedding G).toAlgebra
  let : Module k K := Algebra.toModule
  let g : (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)).RationalPoints :=
    ⟨GenericPoint.Construction.genericSL G, by
      change GenericPoint.Construction.genericSL G ∈ G.subgroup K ((RingHom.id K).comp (GenericPoint.Construction.genericBaseEmbedding G))
      rw [RingHom.id_comp]
      exact GenericPoint.Construction.genericSL_mem G⟩
  have hz (D : Derivation k K K) : D (GenericPoint.Construction.genericCoordinateHom G p) = 0 := by
    have hh := Evaluation.Construction.infinitesimal_invariant_derivation_zero G hG p hp g D
    change D (Algebraic.evaluateMatrix (GenericPoint.Construction.genericBaseEmbedding G) (GenericPoint.Construction.genericSL G) p) = 0 at hh
    rwa [GenericPoint.Construction.evaluate_genericSL] at hh
  obtain ⟨c, hc⟩ := DifferentialConstants.Construction.constant_of_all_derivations_zero (k := k) (K := K) (GenericPoint.Construction.genericCoordinateHom G p) hz
  have hpc : p - MvPolynomial.C c ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G := by
    apply (GenericPoint.Construction.genericCoordinateHom_eq_zero_iff G _).mp
    rw [map_sub]
    exact sub_eq_zero.mpr hc.symm
  have he0 : Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (p - MvPolynomial.C c) = 0 :=
    hpc k (RingHom.id k) (1 : G.RationalPoints)
  have hC : Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (MvPolynomial.C c) = c := by
    simp [Algebraic.evaluateMatrix]
  rw [map_sub, hC, sub_eq_zero] at he0
  rw [he0]
  exact hpc

theorem infinitesimal_invariant_constant
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (p : Algebraic.CoordinatePolynomial n k)
    (hp : ∀ A ∈ Action.Construction.infinitesimalStabilizer G, Action.Construction.rightInfinitesimal A p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G) :
    p - MvPolynomial.C (Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) p) ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G := by
  let K := AlgebraicClosure k
  let H := BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)
  let pK := MvPolynomial.map (algebraMap k K) p
  have hpK : ∀ A ∈ Action.Construction.infinitesimalStabilizer H, Action.Construction.rightInfinitesimal A pK ∈ VanishingIdeal.Construction.coordinateVanishingIdeal H := by
    intro A hA
    apply (BaseChange.Construction.mem_vanishingIdeal_iff_rational_of_algClosed H _).mpr
    intro g
    exact Evaluation.Construction.infinitesimal_invariant_evaluate_baseChange G hG p hp g hA
  have hconst := infinitesimal_invariant_constant_of_algClosed H
    (ConnectedBaseChange.Construction.geometrically_connected_baseChange G hG) pK hpK
  rw [← GeometricIrreducibility.Construction.geometricVanishingIdeal_comap G, Ideal.mem_comap, ConnectedBaseChange.Construction.geometricVanishingIdeal_eq_baseChange_ideal]
  simpa only [pK, H, K, map_sub, MvPolynomial.map_C, CoefficientMap.Construction.evaluate_one_coefficient_map] using hconst

theorem evaluate_infinitesimal_invariant_constant
    {k K : Type} [Field k] [CharZero k] [Field K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (p : Algebraic.CoordinatePolynomial n k)
    (hp : ∀ A ∈ Action.Construction.infinitesimalStabilizer G, Action.Construction.rightInfinitesimal A p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G)
    (ι : k →+* K) (g : G.Points ι) :
    Algebraic.evaluateMatrix ι g.val p = ι (Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) p) := by
  have h := infinitesimal_invariant_constant G hG p hp K ι g
  change Algebraic.evaluateMatrix ι g.val (p - MvPolynomial.C _) = 0 at h
  rw [map_sub] at h
  have hC (c : k) : Algebraic.evaluateMatrix ι g.val (MvPolynomial.C c) = ι c := by simp [Algebraic.evaluateMatrix]
  rw [hC] at h
  exact sub_eq_zero.mp h

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.PolynomialConstants.Construction
