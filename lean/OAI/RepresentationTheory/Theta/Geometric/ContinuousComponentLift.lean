import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveComponent

/-! # Continuous Component Lift -/

namespace OAI.RepresentationTheory.Theta.Geometric.ContinuousComponentLift

noncomputable section

/-! A continuous map from a connected source to a smooth projective
scheme lifts into one actual integral component. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_continuous_projectiveComponent_lift
    {M : Type*} [TopologicalSpace M] [PreconnectedSpace M] [Nonempty M]
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (f : C(M, AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)) :
    ∃ (C : irreducibleComponents P.carrier) (g : C(M, (P.componentVariety C).analyticSpace)),
      ∀ x, g x ≫ P.componentInclusionOver C = f x := by
  let x₀ : M := Classical.choice inferInstance
  obtain ⟨⟨C, p⟩, hp⟩ := P.componentPointsHomeomorph.surjective (f x₀)
  let j := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (P.componentInclusionOver C)
  have ho := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion (P.componentInclusionOver C)
  have hc := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion (P.componentInclusionOver C)
  have hr : IsClopen (Set.range j) := ⟨hc.isClosed_range, ho.isOpen_range⟩
  have hall : f ⁻¹' Set.range j = Set.univ := (hr.preimage f.continuous).eq_univ ⟨x₀, p, hp⟩
  have hmem (x : M) : f x ∈ Set.range j := by
    change x ∈ f ⁻¹' Set.range j
    rw [hall]
    trivial
  let h : C(M, Set.range j) :=
    ⟨fun x => ⟨f x, hmem x⟩, f.continuous.subtype_mk hmem⟩
  let e := ho.isEmbedding.toHomeomorph
  refine ⟨C, (show C(Set.range j, (P.componentVariety C).analyticSpace) from
    ⟨e.symm, e.symm.continuous⟩).comp h, ?_⟩
  intro x
  exact congrArg Subtype.val (e.apply_symm_apply (h x))

end

end OAI.RepresentationTheory.Theta.Geometric.ContinuousComponentLift
