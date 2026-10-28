import OAI.NumberTheory.Quaternion.Arithmetic.AdelicInvariantGap
import OAI.NumberTheory.Quaternion.Arithmetic.SplitCriterion

/-! # Adelic Gap -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AdelicGap

noncomputable section

/-! The nonsplit quaternion case has a uniform positive Minkowski
vector gap over every finite-adelic norm-one lattice and every
archimedean norm-one translate. -/

open scoped Classical _root_.NumberField _root_.Quaternion
open _root_.NumberField _root_.NumberField.mixedEmbedding QuaternionAlgebra

variable {F : Type} [Field F] [NumberField F]

theorem quaternion_nonsplit_uniform_minkowski_gap (a b : F) (ha : a ≠ 0)
    (hs : ¬ ∃ x y : F, x ^ 2 - a * y ^ 2 = b) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (g : FiniteAdelicMatrices.FiniteAdelicGroupPoints (MatrixGroup.quaternionNormOneMatrixGroup a b))
        (h : (MatrixGroup.quaternionNormOneMatrixGroup a b).ArchimedeanProduct Set.univ),
        ∀ x ∈ FiniteAdelicLattice.finiteAdelicMatrixLattice (FiniteAdelicMatrices.finiteAdelicMatrix (MatrixGroup.quaternionNormOneMatrixGroup a b) g),
          x ≠ 0 → ε ≤ ‖ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F 4
            (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv (MatrixGroup.quaternionNormOneMatrixGroup a b) h).val
            (fun i => mixedEmbedding F (x i))‖ := by
  apply AdelicInvariantGap.uniform_minkowski_gap_of_adelic_invariant (MatrixGroup.quaternionNormOneMatrixGroup a b)
    (MatrixGroup.quaternionNormPolynomial a b)
  · simp [MatrixGroup.quaternionNormPolynomial]
  · exact fun v g x => MatrixGroup.quaternionMatrixPoint_preserves_normPolynomial (LocalAdeles.localEmbedding (.inr v)) a b g x
  · exact fun v g x => MatrixGroup.quaternionMatrixPoint_preserves_normPolynomial (algebraMap F v.Completion) a b g x
  · intro x hx hzero
    have he := MatrixGroup.quaternionNormPolynomial_eval (RingHom.id F) a b x
    change MvPolynomial.eval x (MatrixGroup.quaternionNormPolynomial a b) = Norm.quaternionNorm a b (MatrixGroup.quaternionOfCoordinates a b x) at he
    have hq := SplitCriterion.quaternion_norm_anisotropic_of_no_splitting_equation a b ha hs
      (MatrixGroup.quaternionOfCoordinates a b x) (he.symm.trans hzero)
    apply hx
    apply (linearEquivTuple a 0 b).symm.injective
    change MatrixGroup.quaternionOfCoordinates a b x = (linearEquivTuple a 0 b).symm 0
    rw [hq, map_zero]

end

end OAI.NumberTheory.Quaternion.Arithmetic.AdelicGap
