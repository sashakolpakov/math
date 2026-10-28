import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Auxiliary

/-! # Closure Embedding Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ClosureEmbeddingTransport.CM

noncomputable section

/-! Two embeddings of the algebraic closure into the same algebraically
closed field differ by a rational Galois automorphism. Its restriction
is determined by the embeddings on the original coefficient field. -/

open scoped Classical

variable {K : Type} [Field K] [CharZero K] [IsAlgClosed K]

def closureEquiv (ι : CMExtraction.ParameterChoices.Qbar →+* K) : CMExtraction.ParameterChoices.Qbar ≃ₐ[ℚ] algebraicClosure ℚ K := by
  let : IsAlgClosure ℚ CMExtraction.ParameterChoices.Qbar := AlgebraicClosure.instIsAlgClosure ℚ
  let : IsAlgClosure ℚ (algebraicClosure ℚ K) := algebraicClosure.isAlgClosure ℚ K
  let f := ι.toRatAlgHom.codRestrict (algebraicClosure ℚ K).toSubalgebra
    (fun x => mem_algebraicClosure_iff.mpr
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom ι.toRatAlgHom))
  exact AlgEquiv.ofBijective f
    (Algebra.IsAlgebraic.algHom_bijective₂ f
      (IsAlgClosure.equiv ℚ (algebraicClosure ℚ K) CMExtraction.ParameterChoices.Qbar).toAlgHom).1

theorem image (ι : CMExtraction.ParameterChoices.Qbar →+* K) (x : CMExtraction.ParameterChoices.Qbar) : (closureEquiv ι x : K) = ι x := rfl

def transport (ι₁ ι₂ : CMExtraction.ParameterChoices.Qbar →+* K) : Gal(CMExtraction.ParameterChoices.Qbar/ℚ) :=
  (closureEquiv ι₂).trans (closureEquiv ι₁).symm

theorem compatibility (ι₁ ι₂ : CMExtraction.ParameterChoices.Qbar →+* K) (x : CMExtraction.ParameterChoices.Qbar) :
    ι₁ (transport ι₁ ι₂ x) = ι₂ x :=
  congrArg (fun y : algebraicClosure ℚ K => (y : K))
    ((closureEquiv ι₁).apply_symm_apply (closureEquiv ι₂ x))

theorem restriction_eq (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E]
    (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) (ι₁ ι₂ : CMExtraction.ParameterChoices.Qbar →+* K) (a : Gal(E/ℚ))
    (h : ∀ x : E, ι₂ (ιE x) = ι₁ (ιE (a x))) : CMExtraction.ParameterChoices.restriction E ιE (transport ι₁ ι₂) = a := by
  apply AlgEquiv.ext
  intro x
  apply ιE.injective
  apply ι₁.injective
  exact (congrArg ι₁ (CMExtraction.ParameterChoices.restriction_commutes E ιE (transport ι₁ ι₂) x).symm).trans
    ((compatibility ι₁ ι₂ (ιE x)).trans (h x))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ClosureEmbeddingTransport.CM
