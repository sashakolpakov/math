import OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedGeneralLinearAction
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-! # Semisimple Matrix Diagonalization -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.SemisimpleMatrixDiagonalization.Construction

noncomputable section

section

/-! A semisimple matrix over an algebraically closed field admits an
invertible change of basis to a diagonal matrix. -/

open scoped Classical

theorem matrix_conjugate_diagonal_of_eigenbasis
    {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (b : Module.Basis (Fin n) k (Fin n → k)) (w : Fin n → k)
    (hb : ∀ i, Matrix.toLin' A (b i) = w i • b i) :
    ∃ g : Matrix.GeneralLinearGroup (Fin n) k,
      A = g.val * Matrix.diagonal w * (g⁻¹).val := by
  let c := Pi.basisFun k (Fin n)
  let g : Matrix.GeneralLinearGroup (Fin n) k :=
    ⟨c.toMatrix b, b.toMatrix c, c.toMatrix_mul_toMatrix_flip b, b.toMatrix_mul_toMatrix_flip c⟩
  have hd : LinearMap.toMatrix b b (Matrix.toLin' A) = Matrix.diagonal w := by
    ext i j : 1
    by_cases hij : i = j
    · subst j
      simp [LinearMap.toMatrix_apply, hb]
    · simp [LinearMap.toMatrix_apply, hb, hij]
  refine ⟨g, ?_⟩
  change A = c.toMatrix b * Matrix.diagonal w * b.toMatrix c
  rw [← hd, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  exact (LinearMap.toMatrix_toLin c c A).symm

theorem semisimple_matrix_has_eigenbasis
    {k : Type} [Field k] [IsAlgClosed k] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) (hA : Module.End.IsSemisimple (Matrix.toLin' A)) :
    ∃ (b : Module.Basis (Fin n) k (Fin n → k)) (w : Fin n → k),
      ∀ i, Matrix.toLin' A (b i) = w i • b i := by
  let f : Module.End k (Fin n → k) := Matrix.toLin' A
  let eigenDecomp := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    f.eigenspaces_iSupIndep hA.iSup_eigenspace_eq_top
  let I := (a : k) × Fin (Module.finrank k (f.eigenspace a))
  let b : Module.Basis I k (Fin n → k) :=
    eigenDecomp.collectedBasis fun a => Module.finBasis k (f.eigenspace a)
  let : Fintype I := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card I = Fintype.card (Fin n) := by
    simpa using (Module.finrank_eq_card_basis b).symm
  let e : I ≃ Fin n := Fintype.equivOfCardEq hcard
  refine ⟨b.reindex e, fun i => (e.symm i).1, fun i => ?_⟩
  rw [Module.Basis.reindex_apply]
  exact Module.End.mem_eigenspace_iff.mp (eigenDecomp.collectedBasis_mem _ (e.symm i))

theorem semisimple_matrix_conjugate_diagonal
    {k : Type} [Field k] [IsAlgClosed k] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) (hA : Module.End.IsSemisimple (Matrix.toLin' A)) :
    ∃ (g : Matrix.GeneralLinearGroup (Fin n) k) (w : Fin n → k),
      A = g.val * Matrix.diagonal w * (g⁻¹).val := by
  obtain ⟨b, w, hb⟩ := semisimple_matrix_has_eigenbasis A hA
  obtain ⟨g, hg⟩ := matrix_conjugate_diagonal_of_eigenbasis A b w hb
  exact ⟨g, w, hg⟩

theorem boundedInfinitesimal_isSemisimple_of_algClosed
    {k : Type} [Field k] [IsAlgClosed k] {n : ℕ} (d : ℕ)
    (A : Matrix (Fin n) (Fin n) k) (hA : Module.End.IsSemisimple (Matrix.toLin' A)) :
    (Infinitesimal.Degree.Construction.boundedInfinitesimal d A).IsSemisimple := by
  obtain ⟨g, w, rfl⟩ := semisimple_matrix_conjugate_diagonal A hA
  exact BoundedGeneralLinearAction.Construction.boundedInfinitesimal_conjugated_diagonal_isSemisimple d g w

end

/-! Semisimplicity of a matrix over a perfect field survives coefficient
extension, by a separable annihilating polynomial. -/

open scoped Classical

theorem matrix_aeval_map
    {k K : Type} [Field k] [Field K] (ι : k →+* K) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) (p : Polynomial k) :
    (Polynomial.aeval A p).map ι = Polynomial.aeval (A.map ι) (p.map ι) := by
  change (ι.mapMatrix : Matrix (Fin n) (Fin n) k →+* Matrix (Fin n) (Fin n) K)
    (Polynomial.aeval A p) = Polynomial.aeval (ι.mapMatrix A) (p.map ι)
  apply Polynomial.map_aeval_eq_aeval_map
    (ψ := (ι.mapMatrix : Matrix (Fin n) (Fin n) k →+* Matrix (Fin n) (Fin n) K)) (φ := ι)
  ext c i j : 2
  simp [Matrix.algebraMap_matrix_apply, Matrix.map_apply, apply_ite ι]

theorem semisimple_matrix_coefficient_map
    {k K : Type} [Field k] [PerfectField k] [Field K] {n : ℕ}
    (ι : k →+* K) (A : Matrix (Fin n) (Fin n) k)
    (hA : Module.End.IsSemisimple (Matrix.toLin' A)) :
    Module.End.IsSemisimple (Matrix.toLin' (A.map ι)) := by
  let f : Module.End k (Fin n → k) := Matrix.toLin' A
  let p := minpoly k f
  have hp : p.Separable := PerfectField.separable_iff_squarefree.mpr hA.minpoly_squarefree
  have hzero : Polynomial.aeval A p = 0 := by
    apply Matrix.toLinAlgEquiv'.injective
    rw [← Polynomial.aeval_algHom_apply, map_zero]
    exact minpoly.aeval k f
  have hmap : Polynomial.aeval (A.map ι) (p.map ι) = 0 := by
    rw [← matrix_aeval_map, hzero]
    exact Matrix.map_zero ι ι.map_zero
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp.map.squarefree
  change Polynomial.aeval (Matrix.toLinAlgEquiv' (A.map ι)) (p.map ι) = 0
  rw [Polynomial.aeval_algHom_apply, hmap, map_zero]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.SemisimpleMatrixDiagonalization.Construction
