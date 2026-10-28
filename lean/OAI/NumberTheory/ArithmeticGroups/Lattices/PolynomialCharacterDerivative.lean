import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.PolynomialConstants
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Perfect

/-! # Polynomial Character Derivative -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialCharacterDerivative.Construction

noncomputable section

section

/-! The differential of a multiplicative coordinate polynomial is a
Lie-algebra character. -/

open scoped Classical

attribute [local instance] LieRing.ofAssociativeRing

theorem polynomial_character_leftTranslate
    {k : Type} [Field k] [IsAlgClosed k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (p : Algebraic.CoordinatePolynomial n k)
    (hmul : ∀ g h : G.RationalPoints, Algebraic.evaluateMatrix (RingHom.id k) (g * h).val p =
      Algebraic.evaluateMatrix (RingHom.id k) g.val p * Algebraic.evaluateMatrix (RingHom.id k) h.val p)
    (g : G.RationalPoints) :
    LeftTranslation.Construction.leftTranslate (g.val : Matrix (Fin n) (Fin n) k) p -
      MvPolynomial.C (Algebraic.evaluateMatrix (RingHom.id k) g.val p) * p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G := by
  apply (BaseChange.Construction.mem_vanishingIdeal_iff_rational_of_algClosed G _).mpr
  intro h
  rw [map_sub, map_mul, MatrixDifferential.Construction.leftTranslate_evaluate_rational]
  have hC (c : k) : Algebraic.evaluateMatrix (RingHom.id k) h.val (MvPolynomial.C c) = c := by
    simp [Algebraic.evaluateMatrix]
  rw [hC]
  exact sub_eq_zero.mpr (hmul g h)

theorem polynomial_character_infinitesimal_eigen
    {k : Type} [Field k] [IsAlgClosed k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (p : Algebraic.CoordinatePolynomial n k)
    (hmul : ∀ g h : G.RationalPoints, Algebraic.evaluateMatrix (RingHom.id k) (g * h).val p =
      Algebraic.evaluateMatrix (RingHom.id k) g.val p * Algebraic.evaluateMatrix (RingHom.id k) h.val p)
    {A : Matrix (Fin n) (Fin n) k} (hA : A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    Infinitesimal.Action.Construction.rightInfinitesimal A p - MvPolynomial.C (Finite.TangentEquations.Construction.tangentFunctional p A) * p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G := by
  apply (BaseChange.Construction.mem_vanishingIdeal_iff_rational_of_algClosed G _).mpr
  intro g
  have he : Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k)
      (Infinitesimal.Action.Construction.rightInfinitesimal A (LeftTranslation.Construction.leftTranslate (g.val : Matrix (Fin n) (Fin n) k) p -
        MvPolynomial.C (Algebraic.evaluateMatrix (RingHom.id k) g.val p) * p)) = 0 :=
    (Infinitesimal.Action.Construction.mem_infinitesimalStabilizer G A).mp hA _ (polynomial_character_leftTranslate G p hmul g)
      k (RingHom.id k) (1 : G.RationalPoints)
  have hC (x : Algebraic.SL n k) (c : k) : Algebraic.evaluateMatrix (RingHom.id k) x (MvPolynomial.C c) = c := by
    simp [Algebraic.evaluateMatrix]
  rw [map_sub, LeftTranslation.Construction.rightInfinitesimal_leftTranslate, LeftTranslation.Construction.rightInfinitesimal_C_mul,
    map_sub, TangentIdentity.Construction.leftTranslate_evaluate_one, map_mul, hC] at he
  rw [map_sub, map_mul, hC]
  change Algebraic.evaluateMatrix (RingHom.id k) g.val (Infinitesimal.Action.Construction.rightInfinitesimal A p) -
    Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (Infinitesimal.Action.Construction.rightInfinitesimal A p) *
      Algebraic.evaluateMatrix (RingHom.id k) g.val p = 0
  simpa only [mul_comm] using he

theorem polynomial_character_tangent_commutator_zero
    {k : Type} [Field k] [IsAlgClosed k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (p : Algebraic.CoordinatePolynomial n k)
    (hmul : ∀ g h : G.RationalPoints, Algebraic.evaluateMatrix (RingHom.id k) (g * h).val p =
      Algebraic.evaluateMatrix (RingHom.id k) g.val p * Algebraic.evaluateMatrix (RingHom.id k) h.val p)
    {A B : Matrix (Fin n) (Fin n) k}
    (hA : A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G) (hB : B ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    Finite.TangentEquations.Construction.tangentFunctional p ⁅A, B⁆ = 0 := by
  have hiter {U V : Matrix (Fin n) (Fin n) k}
      (hU : U ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G) (hV : V ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
      Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (Infinitesimal.Action.Construction.rightInfinitesimal U (Infinitesimal.Action.Construction.rightInfinitesimal V p)) =
        Finite.TangentEquations.Construction.tangentFunctional p V * Finite.TangentEquations.Construction.tangentFunctional p U := by
    have he : Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k)
        (Infinitesimal.Action.Construction.rightInfinitesimal U (Infinitesimal.Action.Construction.rightInfinitesimal V p - MvPolynomial.C (Finite.TangentEquations.Construction.tangentFunctional p V) * p)) = 0 :=
      (Infinitesimal.Action.Construction.mem_infinitesimalStabilizer G U).mp hU _
        (polynomial_character_infinitesimal_eigen G p hmul hV) k (RingHom.id k) (1 : G.RationalPoints)
    have hC (c : k) : Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (MvPolynomial.C c) = c := by
      simp [Algebraic.evaluateMatrix]
    rw [map_sub, LeftTranslation.Construction.rightInfinitesimal_C_mul, map_sub, map_mul, hC] at he
    exact sub_eq_zero.mp he
  change Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (Infinitesimal.Action.Construction.rightInfinitesimal ⁅A, B⁆ p) = 0
  rw [Infinitesimal.Action.Construction.rightInfinitesimal_bracket, Derivation.commutator_apply, map_sub, hiter hA hB, hiter hB hA]
  ring

end

/-! A multiplicative coordinate polynomial, equal to one at the
identity, is identically one on a connected semisimple Lattices group. The
conclusion holds over every extension field. -/

open scoped Classical

attribute [local instance] LieRing.ofAssociativeRing

theorem polynomial_character_eq_one_of_perfect
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (hperfect : LieAlgebra.derivedSeries k (Infinitesimal.Action.Construction.infinitesimalStabilizer G) 1 = ⊤)
    (p : Algebraic.CoordinatePolynomial n k)
    (hone : Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) p = 1)
    (hmul : ∀ g h : G.RationalPoints, Algebraic.evaluateMatrix (RingHom.id k) (g * h).val p =
      Algebraic.evaluateMatrix (RingHom.id k) g.val p * Algebraic.evaluateMatrix (RingHom.id k) h.val p) :
    p - 1 ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G := by
  let : IsLieAbelian k := ⟨fun x y => sub_eq_zero.mpr (mul_comm x y)⟩
  let f : Infinitesimal.Action.Construction.infinitesimalStabilizer G →ₗ⁅k⁆ k :=
    { toLinearMap := (Finite.TangentEquations.Construction.tangentFunctional p).comp (Infinitesimal.Action.Construction.infinitesimalStabilizer G).toSubmodule.subtype
      map_lie' := by
        intro A B
        change Finite.TangentEquations.Construction.tangentFunctional p ⁅A.val, B.val⁆ =
          ⁅Finite.TangentEquations.Construction.tangentFunctional p A.val, Finite.TangentEquations.Construction.tangentFunctional p B.val⁆
        rw [show (⁅Finite.TangentEquations.Construction.tangentFunctional p A.val, Finite.TangentEquations.Construction.tangentFunctional p B.val⁆ : k) = 0 from
          LieModule.IsTrivial.trivial _ _]
        exact polynomial_character_tangent_commutator_zero G p hmul A.property B.property }
  have hf : f = 0 := PerfectScalarExtension.Construction.perfectLie_hom_to_abelian_eq_zero hperfect f
  have hp : ∀ A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G, Infinitesimal.Action.Construction.rightInfinitesimal A p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G := by
    intro A hA
    have hzero : Finite.TangentEquations.Construction.tangentFunctional p A = 0 := congrArg
      (fun l : Infinitesimal.Action.Construction.infinitesimalStabilizer G →ₗ⁅k⁆ k => l ⟨A, hA⟩) hf
    have he := polynomial_character_infinitesimal_eigen G p hmul hA
    simpa only [hzero, MvPolynomial.C_0, zero_mul, sub_zero] using he
  have hc := Infinitesimal.PolynomialConstants.Construction.infinitesimal_invariant_constant G hG p hp
  simpa only [hone, MvPolynomial.C_1] using hc

theorem polynomial_character_eq_one
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (p : Algebraic.CoordinatePolynomial n k)
    (hone : Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) p = 1)
    (hmul : ∀ (K : Type) [Field K] (ι : k →+* K) (g h : G.Points ι),
      Algebraic.evaluateMatrix ι (g * h).val p = Algebraic.evaluateMatrix ι g.val p * Algebraic.evaluateMatrix ι h.val p) :
    p - 1 ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G := by
  let K := AlgebraicClosure k
  let H := BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)
  let pK := MvPolynomial.map (algebraMap k K) p
  have honeK : Algebraic.evaluateMatrix (RingHom.id K) (1 : Algebraic.SL n K) pK = 1 := by
    rw [Infinitesimal.CoefficientMap.Construction.evaluate_one_coefficient_map, hone, map_one]
  have hmulK : ∀ g h : H.RationalPoints,
      Algebraic.evaluateMatrix (RingHom.id K) (g * h).val pK =
        Algebraic.evaluateMatrix (RingHom.id K) g.val pK * Algebraic.evaluateMatrix (RingHom.id K) h.val pK := by
    intro g h
    simp only [pK, BaseChange.Construction.evaluateMatrix_coefficient_map]
    exact hmul K ((RingHom.id K).comp (algebraMap k K)) g h
  have he := polynomial_character_eq_one_of_perfect H
    (ConnectedBaseChange.Construction.geometrically_connected_baseChange G hconn)
    (Infinitesimal.Perfect.Construction.infinitesimal_baseChange_derived_eq_top G hconn hsemi) pK honeK hmulK
  rw [← GeometricIrreducibility.Construction.geometricVanishingIdeal_comap G, Ideal.mem_comap, ConnectedBaseChange.Construction.geometricVanishingIdeal_eq_baseChange_ideal]
  simpa only [pK, H, K, map_sub, map_one] using he

theorem evaluate_polynomial_character_eq_one
    {k K : Type} [Field k] [CharZero k] [Field K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (p : Algebraic.CoordinatePolynomial n k)
    (hone : Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) p = 1)
    (hmul : ∀ (L : Type) [Field L] (ρ : k →+* L) (g h : G.Points ρ),
      Algebraic.evaluateMatrix ρ (g * h).val p = Algebraic.evaluateMatrix ρ g.val p * Algebraic.evaluateMatrix ρ h.val p)
    (ι : k →+* K) (g : G.Points ι) : Algebraic.evaluateMatrix ι g.val p = 1 := by
  have he := polynomial_character_eq_one G hconn hsemi p hone hmul K ι g
  change Algebraic.evaluateMatrix ι g.val (p - 1) = 0 at he
  rw [map_sub, map_one, sub_eq_zero] at he
  exact he

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialCharacterDerivative.Construction
