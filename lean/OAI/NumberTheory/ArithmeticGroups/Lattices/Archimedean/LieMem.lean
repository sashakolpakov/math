import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.LieEq

/-! # Lie Mem -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.LieMem.Construction

noncomputable section

section

/-! The full archimedean group preserves the real Minkowski Lie space
under matrix conjugation. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.mixedEmbedding

theorem mixedCompletionEvaluation_conjugate
    {k : Type} [Field k] {n : ℕ} (v : InfinitePlace k)
    (g : ExteriorAction.Construction.FullArchimedeanSL k n) (A : Matrix (Fin n) (Fin n) (mixedSpace k)) :
    (Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation v).mapMatrix
      ((Quotient.Construction.archimedeanMixedSL k n g : Matrix (Fin n) (Fin n) (mixedSpace k)) * A *
        (((Quotient.Construction.archimedeanMixedSL k n g)⁻¹ : Algebraic.SL n (mixedSpace k)) : Matrix (Fin n) (Fin n) (mixedSpace k))) =
      (g v : Matrix (Fin n) (Fin n) v.Completion) * A.map (Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation v) *
        (((g v)⁻¹ : Algebraic.SL n v.Completion) : Matrix (Fin n) (Fin n) v.Completion) := by
  have hgi := Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation_matrix v g⁻¹
  rw [map_inv] at hgi
  rw [map_mul, map_mul, Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation_matrix, hgi]
  rfl

theorem archimedean_conjugation_mem_lieMixedSpan
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (g : ExteriorAction.Construction.fullArchimedeanMatrixGroup G)
    (A : Matrix (Fin n) (Fin n) (mixedSpace k)) (hA : A ∈ Lie.MixedLattice.Construction.lieMixedSpan G) :
    (Quotient.Construction.archimedeanMixedSL k n g.val : Matrix (Fin n) (Fin n) (mixedSpace k)) * A *
      (((Quotient.Construction.archimedeanMixedSL k n g.val)⁻¹ : Algebraic.SL n (mixedSpace k)) : Matrix (Fin n) (Fin n) (mixedSpace k)) ∈ Lie.MixedLattice.Construction.lieMixedSpan G := by
  change _ ∈ Lie.MixedLattice.Construction.lieMixedModule G
  apply (Minkowski.LieEq.Construction.lieMixedModule_mem_iff_completions G hG _).mpr
  intro v
  have hAv := (Minkowski.LieEq.Construction.lieMixedModule_mem_iff_completions G hG A).mp hA v
  let H := BaseChange.Construction.matrixGroupBaseChange G (algebraMap k v.Completion)
  let gv : H.RationalPoints := ⟨g.val v, by
    change g.val v ∈ G.subgroup v.Completion ((RingHom.id v.Completion).comp (algebraMap k v.Completion))
    simpa only [RingHom.id_comp] using g.property v⟩
  have h := Infinitesimal.Action.Construction.infinitesimalStabilizer_conjugation H gv hAv
  change (Minkowski.QuadraticInvariant.Construction.mixedCompletionEvaluation v).mapMatrix (_ * _ * _) ∈ _
  rw [mixedCompletionEvaluation_conjugate]
  exact h

end

section

/-! Matrix conjugation by a unit, bundled as a linear equivalence. -/

open scoped Classical

attribute [local instance] LieRing.ofAssociativeRing

def matrixUnitConjugationEquiv
    {R : Type} [CommRing R] {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) R) :
    Matrix (Fin n) (Fin n) R ≃ₗ[R] Matrix (Fin n) (Fin n) R :=
  (Matrix.lieConj g.val g.invertible).toLinearEquiv

theorem matrixUnitConjugationEquiv_apply
    {R : Type} [CommRing R] {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) R)
    (A : Matrix (Fin n) (Fin n) R) :
    matrixUnitConjugationEquiv g A = g.val * A * (g⁻¹).val := by
  change Matrix.lieConj g.val g.invertible A = _
  rw [Matrix.lieConj_apply, Matrix.GeneralLinearGroup.coe_inv]

theorem matrixUnitConjugationEquiv_inverse_apply
    {R : Type} [CommRing R] {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) R)
    (A : Matrix (Fin n) (Fin n) R) :
    matrixUnitConjugationEquiv g⁻¹ (matrixUnitConjugationEquiv g A) = A := by
  rw [matrixUnitConjugationEquiv_apply, matrixUnitConjugationEquiv_apply, inv_inv]
  rw [← mul_assoc, ← mul_assoc, g.inv_mul, one_mul, mul_assoc, g.inv_mul, mul_one]

theorem matrixUnitConjugationEquiv_mul_apply
    {R : Type} [CommRing R] {n : ℕ} (g h : Matrix.GeneralLinearGroup (Fin n) R)
    (A : Matrix (Fin n) (Fin n) R) :
    matrixUnitConjugationEquiv (g * h) A =
      matrixUnitConjugationEquiv g (matrixUnitConjugationEquiv h A) := by
  simp only [matrixUnitConjugationEquiv_apply, Units.val_mul, mul_inv_rev, mul_assoc]

theorem matrixUnitConjugationEquiv_one_apply
    {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    matrixUnitConjugationEquiv (1 : Matrix.GeneralLinearGroup (Fin n) R) A = A := by
  simp only [matrixUnitConjugationEquiv_apply, Units.val_one, inv_one, one_mul, mul_one]

end

/-! The actual full archimedean group acts linearly on the real
Minkowski Lie space by matrix conjugation. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding

def archimedeanLieUnit
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    ExteriorAction.Construction.fullArchimedeanMatrixGroup G →* Matrix.GeneralLinearGroup (Fin n) (mixedSpace k) :=
  Matrix.SpecialLinearGroup.toGL.comp ((Quotient.Construction.archimedeanMixedSL k n).comp (ExteriorAction.Construction.fullArchimedeanMatrixGroup G).subtype)

def archimedeanLieEquiv
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (g : ExteriorAction.Construction.fullArchimedeanMatrixGroup G) : Lie.MixedLattice.Construction.lieMixedSpan G ≃ₗ[ℝ] Lie.MixedLattice.Construction.lieMixedSpan G where
  toFun A := ⟨matrixUnitConjugationEquiv (archimedeanLieUnit G g) A.val, by
    rw [matrixUnitConjugationEquiv_apply]
    exact archimedean_conjugation_mem_lieMixedSpan G hG g A.val A.property⟩
  invFun A := ⟨matrixUnitConjugationEquiv (archimedeanLieUnit G g⁻¹) A.val, by
    rw [matrixUnitConjugationEquiv_apply]
    exact archimedean_conjugation_mem_lieMixedSpan G hG g⁻¹ A.val A.property⟩
  left_inv A := by
    apply Subtype.ext
    change matrixUnitConjugationEquiv (archimedeanLieUnit G g⁻¹)
      (matrixUnitConjugationEquiv (archimedeanLieUnit G g) A.val) = A.val
    rw [map_inv, matrixUnitConjugationEquiv_inverse_apply]
  right_inv A := by
    apply Subtype.ext
    change matrixUnitConjugationEquiv (archimedeanLieUnit G g)
      (matrixUnitConjugationEquiv (archimedeanLieUnit G g⁻¹) A.val) = A.val
    have h := matrixUnitConjugationEquiv_inverse_apply (archimedeanLieUnit G g⁻¹) A.val
    simpa only [map_inv, inv_inv] using h
  map_add' A B := Subtype.ext (map_add _ A.val B.val)
  map_smul' r A := Subtype.ext
    (((matrixUnitConjugationEquiv (archimedeanLieUnit G g)).restrictScalars ℝ).map_smul r A.val)

theorem archimedeanLieEquiv_apply
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (g : ExteriorAction.Construction.fullArchimedeanMatrixGroup G) (A : Lie.MixedLattice.Construction.lieMixedSpan G) :
    (archimedeanLieEquiv G hG g A).val =
      (archimedeanLieUnit G g).val * A.val * ((archimedeanLieUnit G g)⁻¹).val :=
  matrixUnitConjugationEquiv_apply _ _

def archimedeanLieRepresentation
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    ExteriorAction.Construction.fullArchimedeanMatrixGroup G →* (Lie.MixedLattice.Construction.lieMixedSpan G ≃ₗ[ℝ] Lie.MixedLattice.Construction.lieMixedSpan G) where
  toFun := archimedeanLieEquiv G hG
  map_one' := by
    apply LinearEquiv.ext
    intro A
    apply Subtype.ext
    change matrixUnitConjugationEquiv (archimedeanLieUnit G 1) A.val = A.val
    rw [map_one, matrixUnitConjugationEquiv_one_apply]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro A
    apply Subtype.ext
    change matrixUnitConjugationEquiv (archimedeanLieUnit G (g * h)) A.val =
      matrixUnitConjugationEquiv (archimedeanLieUnit G g)
        (matrixUnitConjugationEquiv (archimedeanLieUnit G h) A.val)
    rw [map_mul, matrixUnitConjugationEquiv_mul_apply]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.LieMem.Construction
