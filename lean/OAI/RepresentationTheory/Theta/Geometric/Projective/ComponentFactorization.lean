import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveComponent

/-! # Component Factorization -/

namespace OAI.RepresentationTheory.Theta.Geometric.Projective.ComponentFactorization

noncomputable section

/-! Every map from an integral scheme into a smooth projective scheme
factors through one of its actual open and closed integral components. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_projectiveComponent_factorization
    {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left]
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (f : X ⟶ P.toOver) :
    ∃ (C : irreducibleComponents P.carrier)
      (g : X ⟶ (P.componentVariety C).toOver), g ≫ P.componentInclusionOver C = f := by
  let x : X.left := Classical.choice inferInstance
  obtain ⟨C, hC⟩ := P.componentInclusions_cover (f.left x)
  let i := P.componentInclusionOver C
  have hr : IsClopen (Set.range i.left) :=
    ⟨i.left.isClosedEmbedding.isClosed_range, i.left.isOpenEmbedding.isOpen_range⟩
  have hp : f.left ⁻¹' Set.range i.left = Set.univ :=
    (hr.preimage f.left.continuous).eq_univ ⟨x, hC⟩
  have hs : Set.range f.left ⊆ Set.range i.left := by
    rintro _ ⟨y, rfl⟩
    change y ∈ f.left ⁻¹' Set.range i.left
    rw [hp]
    exact Set.mem_univ y
  let l := IsOpenImmersion.lift i.left f.left hs
  have hl : l ≫ i.left = f.left := IsOpenImmersion.lift_fac _ _ _
  let g : X ⟶ (P.componentVariety C).toOver := Over.homMk l (by
    rw [← i.w, ← Category.assoc, hl]
    exact f.w)
  exact ⟨C, g, Over.OverMorphism.ext hl⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Projective.ComponentFactorization
