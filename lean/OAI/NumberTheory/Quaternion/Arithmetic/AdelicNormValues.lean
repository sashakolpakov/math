import OAI.NumberTheory.Quaternion.Arithmetic.AdelicPolynomialInvariants
import OAI.NumberTheory.Quaternion.Arithmetic.MatrixGroup

/-! # Adelic Norm Values -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AdelicNormValues

noncomputable section

/-! Reduced norms on the lattices attached to finite-adelic quaternion
norm-one points have a denominator independent of the adelic point. -/

open scoped Classical _root_.NumberField

variable {F : Type} [Field F] [NumberField F]

theorem quaternion_finiteAdelic_lattice_norm_integral (a b : F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧
      ∀ g : FiniteAdelicMatrices.FiniteAdelicGroupPoints (MatrixGroup.quaternionNormOneMatrixGroup a b),
        ∀ x ∈ FiniteAdelicLattice.finiteAdelicMatrixLattice (FiniteAdelicMatrices.finiteAdelicMatrix (MatrixGroup.quaternionNormOneMatrixGroup a b) g),
          (d : F) * Norm.quaternionNorm a b (MatrixGroup.quaternionOfCoordinates a b x) ∈ (algebraMap (𝓞 F) F).range := by
  obtain ⟨d, hd, h⟩ := AdelicPolynomialInvariants.finiteAdelicGroupLattice_invariant_values (MatrixGroup.quaternionNormOneMatrixGroup a b)
    (MatrixGroup.quaternionNormPolynomial a b)
    (fun v g x => MatrixGroup.quaternionMatrixPoint_preserves_normPolynomial (LocalAdeles.localEmbedding (.inr v)) a b g x)
  refine ⟨d, hd, ?_⟩
  intro g x hx
  have he := MatrixGroup.quaternionNormPolynomial_eval (RingHom.id F) a b x
  change MvPolynomial.eval x (MatrixGroup.quaternionNormPolynomial a b) = Norm.quaternionNorm a b (MatrixGroup.quaternionOfCoordinates a b x) at he
  rw [← he]
  exact h g x hx

end

end OAI.NumberTheory.Quaternion.Arithmetic.AdelicNormValues
