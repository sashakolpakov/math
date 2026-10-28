import OAI.NumberTheory.Quaternion.Arithmetic.TangentInclusion
import OAI.NumberTheory.Quaternion.Arithmetic.RegularMatrixEmbedding
import OAI.NumberTheory.Quaternion.Arithmetic.MatrixScalarRestriction

/-! # Intrinsic Projection -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.IntrinsicProjection

noncomputable section

/-! Transport arithmetic nonzero tangent directions back through a
faithful finite-dimensional algebra representation. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set _root_.Topology

section

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {ι : Type*} [Fintype ι]

theorem closed_arithmetic_product_intrinsic_projection_nonzero
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
    (v₀ : HeightOneSpectrum (𝓞 F)) (v : ι → HeightOneSpectrum (𝓞 F))
    (hv : Function.Injective v) (haway : ∀ j, Sum.inr (v j) ∉ S) (i : ι)
    [∀ j, Algebra (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)) ((v j).adicCompletion F)]
    [∀ j, FiniteDimensional (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)) ((v j).adicCompletion F)]
    [∀ j, ContinuousSMul (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)) ((v j).adicCompletion F)]
    {D : Type*} [NormedRing D] [NormedAlgebra (v₀.adicCompletion F) D] [CompleteSpace D]
    [FiniteDimensional (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)) D]
    (f : (∀ j, Matrix (Fin n) (Fin n) ((v j).adicCompletion F)) →ₐ[TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)] D)
    (hf : IsClosedEmbedding f)
    (J : Subgroup (∀ j, LocalAdeles.LocalPoints G (Sum.inr (v j))))
    (hJ : IsClosed (J : Set (∀ j, LocalAdeles.LocalPoints G (Sum.inr (v j)))))
    (hΓ : ∀ g : Groups.sIntegralPoints G (insert (Sum.inr (v i)) (S : Set (LocalAdeles.Place F))),
      (fun j => LocalAdeles.diagonalLocal G (Sum.inr (v j)) g.val) ∈ J)
    (hnoncompact : ∃ w : LocalAdeles.Place F, w ∈ S ∧ ¬ CompactSpace (LocalAdeles.LocalPoints G w))
    (hvolume : CompactQuotientProjection.QuotientHasInvariantProbability
      (Ambient.arithmeticAmbientSubgroup G S {⟨Sum.inr (v i), haway i⟩})) :
    ∃ a ∈ Submodule.span (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
      (tangentConeAt (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
        (PrimeBlockDecomposition.finiteMatrixProductHom G v '' (J : Set _)) 1), a i ≠ 0 := by
  let : NontriviallyNormedField (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)) :=
    TangentBracket.finiteClosedPrimeNontriviallyNormedField v₀
  let : NormedAlgebra (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)) D :=
    OrderedProductDerivative.finitePrimeNormedAlgebra v₀ D
  obtain ⟨a, ha, hai⟩ := TangentInclusion.closed_arithmetic_product_tangent_projection_nonzero
    G S v₀ v hv haway i f hf J hJ hΓ hnoncompact hvolume
  refine ⟨a, ?_, hai⟩
  apply (RegularMatrixEmbedding.algebraHom_tangentSpan_image_mem_iff f hf
    (PrimeBlockDecomposition.finiteMatrixProductHom G v '' (J : Set _)) a).mp
  exact ha

end

open scoped _root_.Matrix.Norms.Operator

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {ι : Type*} [Fintype ι]

theorem matrix_arithmetic_product_intrinsic_projection_nonzero
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (S : Finset (LocalAdeles.Place F))
    (v₀ : HeightOneSpectrum (𝓞 F)) (v : ι → HeightOneSpectrum (𝓞 F))
    (hv : Function.Injective v) (haway : ∀ j, Sum.inr (v j) ∉ S) (i : ι)
    [∀ j, Algebra (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)) ((v j).adicCompletion F)]
    [∀ j, FiniteDimensional (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)) ((v j).adicCompletion F)]
    [∀ j, ContinuousSMul (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)) ((v j).adicCompletion F)]
    {d : ℕ}
    (f : (∀ j, Matrix (Fin n) (Fin n) ((v j).adicCompletion F)) →ₐ[TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)]
      Matrix (Fin d) (Fin d) (v₀.adicCompletion F)) (hf : IsClosedEmbedding f)
    (J : Subgroup (∀ j, LocalAdeles.LocalPoints G (Sum.inr (v j))))
    (hJ : IsClosed (J : Set (∀ j, LocalAdeles.LocalPoints G (Sum.inr (v j)))))
    (hΓ : ∀ g : Groups.sIntegralPoints G (insert (Sum.inr (v i)) (S : Set (LocalAdeles.Place F))),
      (fun j => LocalAdeles.diagonalLocal G (Sum.inr (v j)) g.val) ∈ J)
    (hnoncompact : ∃ w : LocalAdeles.Place F, w ∈ S ∧ ¬ CompactSpace (LocalAdeles.LocalPoints G w))
    (hvolume : CompactQuotientProjection.QuotientHasInvariantProbability
      (Ambient.arithmeticAmbientSubgroup G S {⟨Sum.inr (v i), haway i⟩})) :
    ∃ a ∈ Submodule.span (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
      (tangentConeAt (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F))
        (PrimeBlockDecomposition.finiteMatrixProductHom G v '' (J : Set _)) 1), a i ≠ 0 := by
  let : FiniteDimensional (TangentBracket.closedPrimeSubfield (v₀.adicCompletion F)) (v₀.adicCompletion F) :=
    LocalCompletion.finiteCompletion_finiteDimensional_closedPrime v₀
  let D := Matrix (Fin d) (Fin d) (v₀.adicCompletion F)
  let : @CompleteSpace D (inferInstance : NormedRing D).toUniformSpace :=
    FiniteDimensional.complete (v₀.adicCompletion F) D
  exact closed_arithmetic_product_intrinsic_projection_nonzero
    (D := D) G S v₀ v hv haway i
    (MatrixScalarRestriction.matrixAlgHom_primeRestriction (K := v₀.adicCompletion F) (d := d) f)
    (MatrixScalarRestriction.matrixAlgHom_primeRestriction_isClosedEmbedding (K := v₀.adicCompletion F) f hf)
    J hJ hΓ hnoncompact hvolume

end

end OAI.NumberTheory.Quaternion.Arithmetic.IntrinsicProjection
