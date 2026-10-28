import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.OpenCohomology
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.Components

/-! # Components -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Components

noncomputable section

/-! Actual algebraic de Rham cohomology decomposes by the original component inclusions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.OpenCohomology

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [QuasiCompact X.hom]

abbrev componentZariskiSpaces (C : irreducibleComponents X.left) : TopCat.{0} :=
  TopCat.of (Betti.Smooth.Components.componentOver X C).left

def componentZariskiInclusion (C : irreducibleComponents X.left) :
    componentZariskiSpaces X C ⟶ TopCat.of X.left := (Betti.Smooth.Components.componentInclusion X C).left.base

theorem componentZariskiInclusion_open (C : irreducibleComponents X.left) :
    Topology.IsOpenEmbedding (componentZariskiInclusion X C) :=
  (Betti.Smooth.Components.componentInclusion X C).left.isOpenEmbedding

theorem componentZariskiInclusion_closed (C : irreducibleComponents X.left) :
    IsClosed (Set.range (componentZariskiInclusion X C)) :=
  (Betti.Smooth.Components.componentInclusion X C).left.isClosedEmbedding.isClosed_range

def componentAlgebraicDeRhamEquiv (n : ℕ) :
    Sheaves.algebraicDeRham X n ≃ₗ[ℂ]
      (∀ C : irreducibleComponents X.left, Sheaves.algebraicDeRham (Betti.Smooth.Components.componentOver X C) n) :=
  (DisjointDerivedHom.hypercohomologyEquiv
    (componentZariskiInclusion X) (componentZariskiInclusion_open X)
    (componentZariskiInclusion_closed X) (Betti.Smooth.Components.componentInclusions_cover X)
    (Betti.Smooth.Components.componentInclusions_disjoint X) (Sheaves.algebraicDeRhamSheafComplexInt X) (n : ℤ)).trans
      (LinearEquiv.piCongrRight fun C =>
        OpenCohomology.openAlgebraicHypercohomologyEquiv (Betti.Smooth.Components.componentInclusion X C) n)

theorem componentAlgebraicDeRhamEquiv_apply (n : ℕ) (a : Sheaves.algebraicDeRham X n)
    (C : irreducibleComponents X.left) :
    componentAlgebraicDeRhamEquiv X n a C =
      OpenForms.algebraicDeRhamPullback (Betti.Smooth.Components.componentInclusion X C) n a := by
  change OpenCohomology.openAlgebraicHypercohomologyEquiv (Betti.Smooth.Components.componentInclusion X C) n
    (DisjointDerivedHom.hypercohomologyEquiv (componentZariskiInclusion X)
      (componentZariskiInclusion_open X) (componentZariskiInclusion_closed X)
      (Betti.Smooth.Components.componentInclusions_cover X) (Betti.Smooth.Components.componentInclusions_disjoint X)
      (Sheaves.algebraicDeRhamSheafComplexInt X) (n : ℤ) a C) = _
  erw [DisjointDerivedHom.hypercohomologyEquiv_apply]
  exact OpenCohomology.openAlgebraicHypercohomologyEquiv_pullback (Betti.Smooth.Components.componentInclusion X C) n a

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Components
