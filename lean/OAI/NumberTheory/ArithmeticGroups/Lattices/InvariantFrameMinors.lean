import OAI.NumberTheory.ArithmeticGroups.Lattices.LieTrace
import OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialHullSolvable
import OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantMinorPolynomial

/-! # Invariant Frame Minors -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantFrameMinors.Construction

noncomputable section

section

/-! The top minors of a basis of an invariant subspace are fixed by a
connected semisimple matrix group. -/

open scoped Classical

attribute [local instance] LieRing.ofAssociativeRing

local instance invariantFrameLieRingModule {k : Type} [Field k] {n : ℕ}
    (S : LieSubalgebra k (Matrix (Fin n) (Fin n) k)) : LieRingModule S (Fin n → k) :=
  LieRingModule.compLieHom (Fin n → k) (DifferentialHullSolvable.Construction.algebraicMatrixLieRepresentation S)

local instance invariantFrameLieModule {k : Type} [Field k] {n : ℕ}
    (S : LieSubalgebra k (Matrix (Fin n) (Fin n) k)) : LieModule k S (Fin n → k) :=
  LieModule.compLieHom (Fin n → k) (DifferentialHullSolvable.Construction.algebraicMatrixLieRepresentation S)

def invariantFrameLieSubmodule {k : Type} [Field k] {n : ℕ}
    (S : LieSubalgebra k (Matrix (Fin n) (Fin n) k))
    (W : Submodule k (Fin n → k))
    (hW : ∀ A ∈ S, ∀ w ∈ W, A.mulVec w ∈ W) : LieSubmodule k S (Fin n → k) where
  toSubmodule := W
  lie_mem := fun {A w} hw => hW A.val A.property w hw

theorem invariant_basis_frame_trace_zero
    {k : Type} [Field k] [CharZero k] {n r : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hs : G.IsSemisimple)
    (W : Submodule k (Fin n → k))
    (hW : ∀ A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G, ∀ w ∈ W, A.mulVec w ∈ W)
    (b : Module.Basis (Fin r) k W) (A : Matrix (Fin n) (Fin n) k)
    (hA : A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    ∃ C : Matrix (Fin r) (Fin r) k,
      A * Matrix.of (fun i j => (b j).val i) = Matrix.of (fun i j => (b j).val i) * C ∧
      C.trace = 0 := by
  let N := invariantFrameLieSubmodule (Infinitesimal.Action.Construction.infinitesimalStabilizer G) W hW
  let b' : Module.Basis (Fin r) k N := b
  let ρ := LieModule.toEnd k (Infinitesimal.Action.Construction.infinitesimalStabilizer G) N
  let T := ρ ⟨A, hA⟩
  refine ⟨LinearMap.toMatrix b' b' T, ?_, ?_⟩
  · ext i j : 1
    have he := congrArg (fun w : N => w.val i) (b'.sum_repr (T (b' j)))
    change (∑ l, (b'.repr (T (b' j))) l • b l).val i = A.mulVec (b j).val i at he
    simpa only [LinearMap.toMatrix_apply', Matrix.mul_apply, Matrix.of_apply,
      Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, mul_comm, Matrix.mulVec, dotProduct] using he.symm
  · rw [← LinearMap.trace_eq_matrix_trace k b']
    exact LieTrace.Construction.perfectLie_trace_representation_zero (Infinitesimal.Perfect.Construction.infinitesimal_derived_eq_top G hG hs) ρ ⟨A, hA⟩

end

/-! Evaluation of invariant frame minors over arbitrary extension fields. -/

open scoped Classical
open _root_.MvPolynomial

theorem evaluate_frameMinorPolynomial
    {k K : Type} [Field k] [Field K] {n r : ℕ}
    (U : Matrix (Fin n) (Fin r) k) (rows : Fin r → Fin n)
    (ι : k →+* K) (g : Algebraic.SL n K) :
    Algebraic.evaluateMatrix ι g (InvariantMinorPolynomial.Construction.frameMinorPolynomial U rows) =
      (((g : Matrix (Fin n) (Fin n) K) * U.map ι).submatrix rows id).det := by
  rw [InvariantMinorPolynomial.Construction.frameMinorPolynomial, RingHom.map_det]
  congr 1
  ext i j : 1
  simp [InvariantMinorPolynomial.Construction.polynomialColumnMatrix, MatrixDifferential.Construction.matrixVectorPolynomial, Algebraic.evaluateMatrix, Matrix.mul_apply]

theorem group_preserves_invariant_basis_minors
    {k K : Type} [Field k] [CharZero k] [Field K] {n r : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hs : G.IsSemisimple)
    (W : Submodule k (Fin n → k))
    (hW : ∀ A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G, ∀ w ∈ W, A.mulVec w ∈ W)
    (b : Module.Basis (Fin r) k W) (rows : Fin r → Fin n)
    (ι : k →+* K) (g : G.Points ι) :
    (((g.val : Matrix (Fin n) (Fin n) K) *
        (Matrix.of (fun i j => (b j).val i)).map ι).submatrix rows id).det =
      ι ((Matrix.of (fun i j => (b j).val i)).submatrix rows id).det := by
  have h := InvariantMinorPolynomial.Construction.group_preserves_frame_minors G hG (Matrix.of (fun i j => (b j).val i))
    (fun A hA => invariant_basis_frame_trace_zero G hG hs W hW b A hA) rows ι g
  rw [evaluate_frameMinorPolynomial, evaluate_frameMinorPolynomial] at h
  simpa using h

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantFrameMinors.Construction
