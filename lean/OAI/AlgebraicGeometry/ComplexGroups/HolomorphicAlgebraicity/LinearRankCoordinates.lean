import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FiniteHolomorphicRank
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Linear Rank Coordinates -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LinearRankCoordinates.Constructions.FiniteRank

noncomputable section

/-!
# Linear coordinates adapted to a derivative
-/

open Set

theorem exists_rank_coordinates
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    (L : E →L[ℂ] F) :
    ∃ (π : F →L[ℂ] L.toLinearMap.range) (κ : E →L[ℂ] L.toLinearMap.ker)
        (e : E ≃L[ℂ] L.toLinearMap.range × L.toLinearMap.ker),
      (∀ v : L.toLinearMap.range, π v = v) ∧
      e.toContinuousLinearMap = (π.comp L).prod κ := by
  obtain ⟨K, hK⟩ := L.toLinearMap.ker.exists_isCompl
  obtain ⟨R, hR⟩ := L.toLinearMap.range.exists_isCompl
  let π : F →L[ℂ] L.toLinearMap.range :=
    (L.toLinearMap.range.projectionOnto R hR).toContinuousLinearMap
  let κ : E →L[ℂ] L.toLinearMap.ker :=
    (L.toLinearMap.ker.projectionOnto K hK).toContinuousLinearMap
  have hπ (v : L.toLinearMap.range) : π v = v :=
    Submodule.projectionOnto_apply_left hR v
  have hcomp : (π.comp L).toLinearMap = L.toLinearMap.rangeRestrict := by
    apply LinearMap.ext
    intro v
    exact hπ ⟨L v, ⟨v, rfl⟩⟩
  have hcompl : IsCompl L.toLinearMap.rangeRestrict.ker κ.toLinearMap.ker := by
    change IsCompl L.toLinearMap.rangeRestrict.ker (L.toLinearMap.ker.projectionOnto K hK).ker
    rw [LinearMap.ker_rangeRestrict, Submodule.ker_projectionOnto]
    exact hK
  let e₀ := LinearMap.equivProdOfSurjectiveOfIsCompl L.toLinearMap.rangeRestrict κ.toLinearMap
    L.toLinearMap.range_rangeRestrict (Submodule.range_projectionOnto hK) hcompl
  refine ⟨π, κ, e₀.toContinuousLinearEquiv, hπ, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  change (L.toLinearMap.rangeRestrict v, κ v) = ((π.comp L) v, κ v)
  have h := congrArg (fun T : E →ₗ[ℂ] L.toLinearMap.range => T v) hcomp
  exact Prod.ext h.symm rfl

theorem finrank_range_comp_le_middle
    {E F G H : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [AddCommGroup G] [Module ℂ G] [FiniteDimensional ℂ G]
    [AddCommGroup H] [Module ℂ H] [FiniteDimensional ℂ H]
    (A : G →ₗ[ℂ] H) (L : F →ₗ[ℂ] G) (B : E →ₗ[ℂ] F) :
    Module.finrank ℂ (A.comp (L.comp B)).range ≤ Module.finrank ℂ L.range := by
  let T : L.range →ₗ[ℂ] H := A.comp L.range.subtype
  have hsub : (A.comp (L.comp B)).range ≤ T.range := by
    rintro _ ⟨v, rfl⟩
    exact ⟨⟨L (B v), ⟨B v, rfl⟩⟩, rfl⟩
  exact (Submodule.finrank_mono hsub).trans (LinearMap.finrank_range_le T)

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LinearRankCoordinates.Constructions.FiniteRank
