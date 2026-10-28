import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Compact Isometry -/

namespace OAI.Analysis.HodgeTheory.Decomposition.CompactIsometry.Constructions

noncomputable section

/-! A compact inner-product-preserving inclusion has finite-dimensional domain. -/

theorem submodule_projection_inner_ambient {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (K : Submodule ℂ E) [CompleteSpace K] (u : E) (k : K) :
    inner ℂ (K.orthogonalProjectionOnto u).val k.val = inner ℂ u k.val :=
  Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right k u

theorem finiteDimensional_of_compact_inner_preserving {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (J : E →L[ℂ] F) (hJ : IsCompactOperator J)
    (hinner : ∀ u v, inner ℂ (J u) (J v) = inner ℂ u v) : FiniteDimensional ℂ E := by
  have hleft : J.adjoint.comp J = ContinuousLinearMap.id ℂ E := by
    apply ContinuousLinearMap.ext
    intro u
    apply ext_inner_right ℂ
    intro v
    change inner ℂ (J.adjoint (J u)) v = inner ℂ u v
    exact (ContinuousLinearMap.adjoint_inner_left J v (J u)).trans (hinner u v)
  have hcompact := hJ.clm_comp J.adjoint
  change IsCompactOperator (J.adjoint.comp J) at hcompact
  rw [hleft] at hcompact
  exact FiniteDimensional.of_isCompactOperator_id (𝕜 := ℂ) hcompact

end

end OAI.Analysis.HodgeTheory.Decomposition.CompactIsometry.Constructions
