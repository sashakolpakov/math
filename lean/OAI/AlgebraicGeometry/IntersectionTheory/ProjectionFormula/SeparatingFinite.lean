import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FiberCutInduction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.FiberEquations
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.EtaleNeighborhoods

/-! # Separating Finite -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SeparatingFinite

noncomputable section

/-! A finite projection can simultaneously be etale at selected closed
points and separate each point from the rest of a positive-codimension support. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Projection

attribute [local instance] PointJetCoordinates.scalar

theorem exists_points (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    {ι : Type} [Finite ι] (p : ι → (Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X.carrier))
    (hp : ∀ j, p j ≫ X.structureMap = 𝟙 _)
    (Z : ι → Closeds X.carrier)
    (hZ : ∀ j, ∀ W : IrreducibleCloseds X.carrier,
      (W : Set X.carrier) ⊆ Z j → 1 ≤ X.supportCodimension W) :
    ∃ π : X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m,
      π ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m = X.structureMap ∧ IsFinite π ∧
      ∀ j, (∃ U : X.carrier.Opens, p j (IsLocalRing.closedPoint ℂ) ∈ U ∧ Etale (U.ι ≫ π)) ∧
        ∀ y ∈ Z j, π y = π (p j (IsLocalRing.closedPoint ℂ)) → y = p j (IsLocalRing.closedPoint ℂ) := by
  let D j := (PointJetCoordinates.equivalence X (p j) (hp j) m).toLinearMap.comp
    (PointJetCoordinates.map X (p j) (hp j))
  have hD : ∀ j, Function.Surjective (D j) := fun j =>
    (PointJetCoordinates.equivalence X (p j) (hp j) m).surjective.comp
      (PointJetCoordinates.surjective X (p j) (hp j))
  obtain ⟨s, L, hLs, _, h, hfiber, hLI⟩ :=
    FiberCutInduction.SeparatingForms.exists_forms X m p hp D hD Z hZ
  let π := Projection.FiniteProjective.FromForms.map X m L h
  have hover : π ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m = X.structureMap :=
    Projection.FiniteProjective.FromForms.over_base X m L h
  refine ⟨π, hover, inferInstance, fun j => ⟨?_, ?_⟩⟩
  · have hi : LinearIndependent ℂ (fun a => PointJetCoordinates.map X (p j) (hp j) (L a)) :=
      LinearIndependent.of_comp (PointJetCoordinates.equivalence X (p j) (hp j) m).toLinearMap (hLI j)
    have hspan : Submodule.span ℂ
        (Set.range (fun a => PointJetCoordinates.map X (p j) (hp j) (L a))) = ⊤ := by
      let := PointJetCoordinates.finite X (p j) (hp j) m
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_eq_card hi, Fintype.card_fin,
        PointJetCoordinates.dimension X (p j) (hp j) m]
    have hu := Projection.StalkUnramified.unramified X m L h (p j) (hp j) hspan
    let := Projective.Dimension.projective_relativeDimension m
    have he := Smooth.EqualDimensionEtale.stalk π X.structureMap (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)
      hover m (p j (IsLocalRing.closedPoint ℂ)) hu
    exact ProjectionFormula.Etale.StalkNeighborhood.exists_open π (p j (IsLocalRing.closedPoint ℂ)) he
  · intro y hy he
    obtain ⟨i, hi⟩ := hLs
    apply hfiber j
    refine ⟨hy, (Projective.LinearCut.mem_commonZero X.embedding _ y).mpr ?_⟩
    intro a
    have ha := Projection.FiberEquations.fiber_equations X m L h (p j) (hp j) i y he a
    rwa [hi] at ha

theorem exists_closed_points (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    {ι : Type} [Finite ι] (x : ι → X.carrier) (hx : ∀ j, IsClosed {x j})
    (Z : ι → Closeds X.carrier)
    (hZ : ∀ j, ∀ W : IrreducibleCloseds X.carrier,
      (W : Set X.carrier) ⊆ Z j → 1 ≤ X.supportCodimension W) :
    ∃ π : X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m,
      π ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m = X.structureMap ∧ IsFinite π ∧
      ∀ j, (∃ U : X.carrier.Opens, x j ∈ U ∧ Etale (U.ι ≫ π)) ∧
        ∀ y ∈ Z j, π y = π (x j) → y = x j := by
  let p j := pointOfClosedPoint X.structureMap (x j) (hx j)
  have hp j : p j ≫ X.structureMap = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  obtain ⟨π, hover, hfinite, hπ⟩ := exists_points X m p hp Z hZ
  refine ⟨π, hover, hfinite, fun j => ?_⟩
  have he : p j (IsLocalRing.closedPoint ℂ) = x j := pointOfClosedPoint_apply _ _ _ _
  simpa only [he] using hπ j

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SeparatingFinite
