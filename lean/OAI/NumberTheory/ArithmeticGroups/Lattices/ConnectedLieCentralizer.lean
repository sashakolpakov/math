import OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixDerivation
import OAI.NumberTheory.ArithmeticGroups.Lattices.ConjugationCoordinatePolynomial
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.TangentExtension

/-! # Connected Lie Centralizer -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ConnectedLieCentralizer.Construction

noncomputable section

/-! For a connected characteristic-zero algebraic matrix group, a
matrix commuting with its Lie algebra commutes with the group. -/

open scoped Classical

theorem conjugation_constant_of_infinitesimal_algClosed
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (C : Matrix (Fin n) (Fin n) k)
    (hC : ∀ A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G, A * C = C * A)
    (i j : Fin n) :
    ConjugationCoordinatePolynomial.Construction.matrixConjugationPolynomial C i j - MvPolynomial.C (C i j) ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G := by
  let : (VanishingIdeal.Construction.coordinateVanishingIdeal G).IsPrime := GeometricIrreducibility.Construction.coordinateVanishingIdeal_isPrime G hG
  let K := GenericPoint.Construction.MatrixFunctionField G
  let : Algebra k K := (GenericPoint.Construction.genericBaseEmbedding G).toAlgebra
  let : Module k K := Algebra.toModule
  let g : (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)).RationalPoints :=
    ⟨GenericPoint.Construction.genericSL G, by
      change GenericPoint.Construction.genericSL G ∈ G.subgroup K ((RingHom.id K).comp (GenericPoint.Construction.genericBaseEmbedding G))
      rw [RingHom.id_comp]
      exact GenericPoint.Construction.genericSL_mem G⟩
  let p := ConjugationCoordinatePolynomial.Construction.matrixConjugationPolynomial C i j
  have hz (D : Derivation k K K) : D (GenericPoint.Construction.genericCoordinateHom G p) = 0 := by
    have hcomm := Infinitesimal.TangentExtension.Construction.infinitesimal_commuting_baseChange (K := K) G hG C hC
      (MatrixDerivation.Construction.logarithmicMatrixDerivative_mem G hG D g)
    have hD := MatrixDerivation.Construction.matrix_derivation_conjugation_zero D g.val C hcomm
    have he := congrArg (fun M => M i j) hD
    change D (((GenericPoint.Construction.genericSL G : Matrix (Fin n) (Fin n) K) * C.map (algebraMap k K) *
      ((GenericPoint.Construction.genericSL G)⁻¹ : Algebraic.SL n K)) i j) = 0 at he
    rw [← GenericPoint.Construction.evaluate_genericSL]
    change D (Algebraic.evaluateMatrix (algebraMap k K) (GenericPoint.Construction.genericSL G) (ConjugationCoordinatePolynomial.Construction.matrixConjugationPolynomial C i j)) = 0
    rw [ConjugationCoordinatePolynomial.Construction.evaluate_matrixConjugationPolynomial_entry]
    exact he
  obtain ⟨c, hc⟩ := DifferentialConstants.Construction.constant_of_all_derivations_zero (k := k) (K := K)
    (GenericPoint.Construction.genericCoordinateHom G p) hz
  have hp : p - MvPolynomial.C c ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G := by
    apply (GenericPoint.Construction.genericCoordinateHom_eq_zero_iff G _).mp
    rw [map_sub]
    exact sub_eq_zero.mpr hc.symm
  have h1 := hp k (RingHom.id k) (1 : G.RationalPoints)
  change Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (p - MvPolynomial.C c) = 0 at h1
  rw [map_sub] at h1
  have hp1 : Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) p = C i j := by
    rw [show p = ConjugationCoordinatePolynomial.Construction.matrixConjugationPolynomial C i j from rfl,
      ConjugationCoordinatePolynomial.Construction.evaluate_matrixConjugationPolynomial_entry]
    simp only [Matrix.SpecialLinearGroup.coe_one, inv_one, Matrix.map_apply,
      Matrix.one_mul, Matrix.mul_one, RingHom.id_apply]
  have hc1 : Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (MvPolynomial.C c) = c := by
    simp [Algebraic.evaluateMatrix]
  rw [hp1, hc1, sub_eq_zero] at h1
  exact h1 ▸ hp

theorem conjugation_constant_of_infinitesimal
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (C : Matrix (Fin n) (Fin n) k)
    (hC : ∀ A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G, A * C = C * A)
    (i j : Fin n) :
    ConjugationCoordinatePolynomial.Construction.matrixConjugationPolynomial C i j - MvPolynomial.C (C i j) ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G := by
  let K := AlgebraicClosure k
  let H := BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)
  have hCK : ∀ A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer H,
      A * C.map (algebraMap k K) = C.map (algebraMap k K) * A :=
    fun _ hA => Infinitesimal.TangentExtension.Construction.infinitesimal_commuting_baseChange G hG C hC hA
  have hp := conjugation_constant_of_infinitesimal_algClosed H
    (ConnectedBaseChange.Construction.geometrically_connected_baseChange G hG) (C.map (algebraMap k K)) hCK i j
  rw [← GeometricIrreducibility.Construction.geometricVanishingIdeal_comap G, Ideal.mem_comap, ConnectedBaseChange.Construction.geometricVanishingIdeal_eq_baseChange_ideal]
  have he : MvPolynomial.map (algebraMap k K) (ConjugationCoordinatePolynomial.Construction.matrixConjugationPolynomial C i j) =
      ConjugationCoordinatePolynomial.Construction.matrixConjugationPolynomial (C.map (algebraMap k K)) i j :=
    congrArg (fun M => M i j) (ConjugationCoordinatePolynomial.Construction.matrixConjugationPolynomial_coefficient_map (algebraMap k K) C)
  rw [map_sub, MvPolynomial.map_C, he]
  exact hp

theorem group_conjugation_eq_of_infinitesimal_commuting
    {k K : Type} [Field k] [CharZero k] [Field K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (C : Matrix (Fin n) (Fin n) k)
    (hC : ∀ A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G, A * C = C * A)
    (ι : k →+* K) (g : G.Points ι) :
    (g.val : Matrix (Fin n) (Fin n) K) * C.map ι *
      ((g.val⁻¹ : Algebraic.SL n K) : Matrix (Fin n) (Fin n) K) = C.map ι := by
  ext i j
  have hp := conjugation_constant_of_infinitesimal G hG C hC i j K ι g
  change Algebraic.evaluateMatrix ι g.val (ConjugationCoordinatePolynomial.Construction.matrixConjugationPolynomial C i j - MvPolynomial.C (C i j)) = 0 at hp
  rw [map_sub, ConjugationCoordinatePolynomial.Construction.evaluate_matrixConjugationPolynomial_entry] at hp
  have hc : Algebraic.evaluateMatrix ι g.val (MvPolynomial.C (C i j)) = ι (C i j) := by
    simp [Algebraic.evaluateMatrix]
  rw [hc, sub_eq_zero] at hp
  exact hp

theorem group_commutes_of_infinitesimal_commuting
    {k K : Type} [Field k] [CharZero k] [Field K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (C : Matrix (Fin n) (Fin n) k)
    (hC : ∀ A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G, A * C = C * A)
    (ι : k →+* K) (g : G.Points ι) :
    (g.val : Matrix (Fin n) (Fin n) K) * C.map ι =
      C.map ι * (g.val : Matrix (Fin n) (Fin n) K) := by
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) K =>
    M * (g.val : Matrix (Fin n) (Fin n) K))
    (group_conjugation_eq_of_infinitesimal_commuting G hG C hC ι g)
  simpa only [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one] using he

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ConnectedLieCentralizer.Construction
