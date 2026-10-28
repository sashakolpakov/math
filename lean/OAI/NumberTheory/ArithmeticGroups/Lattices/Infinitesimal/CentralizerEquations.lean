import OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointKernelCenter
import OAI.NumberTheory.ArithmeticGroups.Lattices.AlgebraicLocusBaseChange

/-! # Centralizer Equations -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.CentralizerEquations.Construction

noncomputable section

/-! Rational polynomial equations for the centralizer of the Lie algebra. -/

open scoped Classical
open _root_.MvPolynomial

attribute [local instance] LieRing.ofAssociativeRing

def matrixCommutatorPolynomial
    {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k) :
    Matrix (Fin n) (Fin n) (Algebraic.CoordinatePolynomial n k) :=
  ConjugationCoordinatePolynomial.Construction.conjugationUniversalMatrix k n * A.map MvPolynomial.C -
    A.map MvPolynomial.C * ConjugationCoordinatePolynomial.Construction.conjugationUniversalMatrix k n

theorem evaluate_matrixCommutatorPolynomial
    {k K : Type} [Field k] [Field K] {n : ℕ}
    (ι : k →+* K) (g : Algebraic.SL n K) (A : Matrix (Fin n) (Fin n) k) :
    (Algebraic.evaluateMatrix ι g).mapMatrix (matrixCommutatorPolynomial A) =
      (g : Matrix (Fin n) (Fin n) K) * A.map ι - A.map ι * (g : Matrix (Fin n) (Fin n) K) := by
  have hX : (Algebraic.evaluateMatrix ι g).mapMatrix (ConjugationCoordinatePolynomial.Construction.conjugationUniversalMatrix k n) =
      (g : Matrix (Fin n) (Fin n) K) := by
    ext i j
    change Algebraic.evaluateMatrix ι g (X (i, j)) = _
    simp [Algebraic.evaluateMatrix]
  have hA : (Algebraic.evaluateMatrix ι g).mapMatrix (A.map MvPolynomial.C) = A.map ι := by
    ext i j
    simp [Algebraic.evaluateMatrix]
  rw [matrixCommutatorPolynomial, map_sub, map_mul, map_mul, hX, hA]

def infinitesimalCentralizerEquations
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    Set (Algebraic.CoordinatePolynomial n k) :=
  insert (CoordinateIdeal.Construction.determinantEquation k n)
    (G.equations ∪ {p | ∃ A ∈ Action.Construction.infinitesimalStabilizer G, ∃ i j, p = matrixCommutatorPolynomial A i j})

def infinitesimalCentralizerIdeal
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    Ideal (Algebraic.CoordinatePolynomial n k) := Ideal.span (infinitesimalCentralizerEquations G)

theorem infinitesimalCentralizer_zeroLocus_point
    {k K : Type} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) {x : (Fin n × Fin n) → K}
    (hx : x ∈ zeroLocus K (infinitesimalCentralizerIdeal G)) :
    ∃ g : G.Points (algebraMap k K), (∀ i j, g.val i j = x (i, j)) ∧
      ∀ A ∈ Action.Construction.infinitesimalStabilizer G,
        (g.val : Matrix (Fin n) (Fin n) K) * A.map (algebraMap k K) =
          A.map (algebraMap k K) * (g.val : Matrix (Fin n) (Fin n) K) := by
  have hp : ∀ p ∈ infinitesimalCentralizerEquations G, aeval x p = 0 :=
    fun p hp => hx p (Ideal.subset_span hp)
  have hd := hp (CoordinateIdeal.Construction.determinantEquation k n) (Set.mem_insert _ _)
  have hdet : Matrix.det (fun i j : Fin n => x (i, j)) = 1 := by
    apply sub_eq_zero.mp
    simpa only [aeval_eq_eval₂Hom, CoordinateIdeal.Construction.eval_determinantEquation] using hd
  let g : Algebraic.SL n K := ⟨fun i j => x (i, j), hdet⟩
  have hg : g ∈ G.subgroup K (algebraMap k K) := by
    apply (G.mem_iff K (algebraMap k K) g).mpr
    intro p hpG
    exact hp p (Set.mem_insert_of_mem _ (Or.inl hpG))
  refine ⟨⟨g, hg⟩, fun _ _ => rfl, ?_⟩
  intro A hA
  apply sub_eq_zero.mp
  rw [← evaluate_matrixCommutatorPolynomial]
  ext i j
  exact hp _ (Set.mem_insert_of_mem _ (Or.inr ⟨A, hA, i, j, rfl⟩))

theorem point_mem_infinitesimalCentralizer_zeroLocus
    {k K : Type} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (g : G.Points (algebraMap k K))
    (hg : ∀ A ∈ Action.Construction.infinitesimalStabilizer G,
      (g.val : Matrix (Fin n) (Fin n) K) * A.map (algebraMap k K) =
        A.map (algebraMap k K) * (g.val : Matrix (Fin n) (Fin n) K)) :
    (fun ij => g.val ij.1 ij.2) ∈ zeroLocus K (infinitesimalCentralizerIdeal G) := by
  rw [infinitesimalCentralizerIdeal, zeroLocus_span]
  intro p hp
  rcases hp with rfl | hp
  · change Algebraic.evaluateMatrix (algebraMap k K) g.val (CoordinateIdeal.Construction.determinantEquation k n) = 0
    simp only [Algebraic.evaluateMatrix, CoordinateIdeal.Construction.eval_determinantEquation, Matrix.SpecialLinearGroup.det_coe, sub_self]
  · rcases hp with hp | ⟨A, hA, i, j, rfl⟩
    · exact (G.mem_iff K (algebraMap k K) g.val).mp g.property p hp
    · have he := congrArg (fun M => M i j) (evaluate_matrixCommutatorPolynomial (algebraMap k K) g.val A)
      rw [hg A hA, sub_self] at he
      exact he

theorem commutes_infinitesimal_extension_of_commutes_base
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (C : Matrix (Fin n) (Fin n) K)
    (hC : ∀ A ∈ Action.Construction.infinitesimalStabilizer G,
      C * A.map (algebraMap k K) = A.map (algebraMap k K) * C)
    {A : Matrix (Fin n) (Fin n) K}
    (hA : A ∈ Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K))) :
    C * A = A * C := by
  change A ∈ (Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K))).toSubmodule at hA
  rw [TangentExtension.Construction.infinitesimalStabilizer_eq_span_base G hG] at hA
  induction hA using Submodule.span_induction with
  | mem A hA => obtain ⟨A, hA, rfl⟩ := hA; exact hC A hA
  | zero => rw [Matrix.mul_zero, Matrix.zero_mul]
  | add A B _ _ hA hB => rw [Matrix.mul_add, Matrix.add_mul, hA, hB]
  | smul a A _ hA => rw [Matrix.mul_smul, Matrix.smul_mul, hA]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.CentralizerEquations.Construction
