import OAI.NumberTheory.Quaternion.Arithmetic.FiniteAdelicMatrices

/-! # Adelic Polynomial Invariants -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AdelicPolynomialInvariants

noncomputable section

/-! Polynomial invariance over each finite completion implies the
corresponding identity in the actual finite-adelic matrix representation. -/

open scoped Classical _root_.NumberField _root_.Matrix
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem finiteAdelicMatrix_polynomial_invariant (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (p : MvPolynomial (Fin n) F)
    (hp : ∀ (v : HeightOneSpectrum (𝓞 F)) (h : LocalAdeles.LocalPoints G (.inr v)) (y : Fin n → v.adicCompletion F),
      MvPolynomial.eval₂Hom (LocalAdeles.localEmbedding (.inr v)) (h.val.val *ᵥ y) p =
        MvPolynomial.eval₂Hom (LocalAdeles.localEmbedding (.inr v)) y p)
    (g : FiniteAdelicMatrices.FiniteAdelicGroupPoints G) (x : Fin n → F) :
    MvPolynomial.eval₂Hom (algebraMap F (ScalarApproximation.ScalarFiniteAdeles F))
      (FiniteAdelicMatrices.finiteAdelicMatrix G g *ᵥ FiniteAdelicLattice.rationalFiniteAdelicVectorMap n x) p =
        algebraMap F (ScalarApproximation.ScalarFiniteAdeles F) (MvPolynomial.eval x p) := by
  apply RestrictedProduct.ext
  intro v
  let π := FiniteAdelicMatrices.scalarFiniteAdeleEvaluation v
  have hρ : π.comp (algebraMap F (ScalarApproximation.ScalarFiniteAdeles F)) = LocalAdeles.localEmbedding (.inr v) := rfl
  have hv : (fun i => π ((FiniteAdelicMatrices.finiteAdelicMatrix G g *ᵥ FiniteAdelicLattice.rationalFiniteAdelicVectorMap n x) i)) =
      (g v).val.val *ᵥ (fun i => LocalAdeles.localEmbedding (.inr v) (x i)) := by
    funext i
    exact RingHom.map_mulVec π (FiniteAdelicMatrices.finiteAdelicMatrix G g) (FiniteAdelicLattice.rationalFiniteAdelicVectorMap n x) i
  change π (MvPolynomial.eval₂Hom (algebraMap F (ScalarApproximation.ScalarFiniteAdeles F))
    (FiniteAdelicMatrices.finiteAdelicMatrix G g *ᵥ FiniteAdelicLattice.rationalFiniteAdelicVectorMap n x) p) =
      π (algebraMap F (ScalarApproximation.ScalarFiniteAdeles F) (MvPolynomial.eval x p))
  rw [MvPolynomial.map_eval₂Hom, hρ, hv]
  apply (hp v (g v) (fun i => LocalAdeles.localEmbedding (.inr v) (x i))).trans
  change MvPolynomial.eval₂Hom (LocalAdeles.localEmbedding (.inr v))
    (fun i => LocalAdeles.localEmbedding (.inr v) (x i)) p = LocalAdeles.localEmbedding (.inr v) (MvPolynomial.eval x p)
  symm
  exact MvPolynomial.map_eval₂Hom (RingHom.id F) x (LocalAdeles.localEmbedding (.inr v)) p

theorem finiteAdelicGroupLattice_invariant_values (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (p : MvPolynomial (Fin n) F)
    (hp : ∀ (v : HeightOneSpectrum (𝓞 F)) (h : LocalAdeles.LocalPoints G (.inr v)) (y : Fin n → v.adicCompletion F),
      MvPolynomial.eval₂Hom (LocalAdeles.localEmbedding (.inr v)) (h.val.val *ᵥ y) p =
        MvPolynomial.eval₂Hom (LocalAdeles.localEmbedding (.inr v)) y p) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ g : FiniteAdelicMatrices.FiniteAdelicGroupPoints G,
      ∀ x ∈ FiniteAdelicLattice.finiteAdelicMatrixLattice (FiniteAdelicMatrices.finiteAdelicMatrix G g),
        (d : F) * MvPolynomial.eval x p ∈ (algebraMap (𝓞 F) F).range := by
  obtain ⟨d, hd, h⟩ := FiniteAdelicPolynomialValues.invariant_adelic_polynomial_rational_values p
  exact ⟨d, hd, fun g => h (FiniteAdelicMatrices.finiteAdelicMatrix G g) (finiteAdelicMatrix_polynomial_invariant G p hp g)⟩

end

end OAI.NumberTheory.Quaternion.Arithmetic.AdelicPolynomialInvariants
