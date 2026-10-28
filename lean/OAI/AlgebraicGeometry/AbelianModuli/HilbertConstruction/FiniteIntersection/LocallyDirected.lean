import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.BaseChangePullbacks
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection.ConcreteOverlapDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Locally.DirectedPullbackDiagram

/-! # Locally Directed -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection

noncomputable section

/-! After the finite overlap-isomorphism extension, the intersection diagram satisfies gluing hypotheses. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Over (Spec (.of R))}
variable [CompactSpace X.left] [IsSeparated X.hom] (M : IntersectionModel.FiniteIntersectionModel X)

theorem IntersectionModel.FiniteIntersectionModel.baseChangedSchemeFunctor_isLocallyDirected (D : Subalgebra M.coefficients R)
    (hD : ∀ j, IsIso ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap M.coefficients D)))).map (M.spanComparison j))) :
    (M.baseChangedSchemeFunctor D ⋙ Scheme.forget).IsLocallyDirected := by
  apply Locally.DirectedPullbackDiagram.schemeDiagram_isLocallyDirected_of_pullbacks
  intro T U S hTS hUS
  let hST : S.val ⊆ T.val := leOfHom hTS
  let hSU : S.val ⊆ U.val := leOfHom hUS
  let j : SpanIndex.finiteIntersectionSpanIndex X := ⟨(S, T, U), hST, hSU⟩
  have : IsIso ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap M.coefficients D)))).map
      (M.overlapComparisonOver hST hSU)) := hD j
  refine ⟨Unions.finiteIntersectionUnion X T U,
    homOfLE (Unions.finiteIntersection_subset_union_left X T U),
    homOfLE (Unions.finiteIntersection_subset_union_right X T U), ?_⟩
  exact M.baseChanged_overlap_isPullback D hST hSU

theorem IntersectionModel.FiniteIntersectionModel.exists_locallyDirected_extension (E : Subalgebra M.coefficients R) (hE : E.FG) :
    ∃ D : Subalgebra M.coefficients R, E ≤ D ∧ D.FG ∧
      (M.baseChangedSchemeFunctor D ⋙ Scheme.forget).IsLocallyDirected := by
  obtain ⟨D, hED, hD, hd⟩ := M.exists_common_overlap_pullback_isIso E hE
  exact ⟨D, hED, hD, M.baseChangedSchemeFunctor_isLocallyDirected D hd⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FiniteIntersection
