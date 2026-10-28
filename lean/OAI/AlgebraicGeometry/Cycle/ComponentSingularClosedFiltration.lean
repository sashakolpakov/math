/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicGeometry.Stratification.ClosedFiltration
import OAI.AlgebraicGeometry.Smooth.SingularLocusDimension
import OAI.Topology.Dimension.ClosedSubset
import Mathlib.Topology.NoetherianSpace
import OAI.AlgebraicGeometry.Stratification.AnalytificationIs
import OAI.AlgebraicGeometry.Smooth.AffineRelativeDimension
import OAI.AlgebraicGeometry.ComplexPoint.Open
import OAI.CategoryTheory.ConcreteCategory.Notation

/-! # Component Singular Closed Filtration -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Ambient closed supports for singular-component localization induction

The singular boundary of an integral cycle component carries its canonical finite reduced
smooth filtration, whose images are closed both algebraically and analytically in the ambient
variety, and whose successive differences are the complex-point images of smooth locally
closed strata. Their local relative dimensions are strictly below `d - p`, so their ambient
normal codimensions are at least `p + 1`.
-/

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left)

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the reduced closure of
the scheme point `x`. Start with `S₀ = Z_sing` and obtain `S_{k+1}` by removing the smooth locus
of the reduced scheme on `S_k`. This is the closed subset `S_k` of `Z`, for a natural number
`k`. -/
abbrev Cycle.ComponentSingularClosedFiltration.cycleComponentSingularClosedFiltration (k : ℕ) : Closeds (Cycle.Support.cycleComponent X.left x) :=
  Stratification.Basic.reducedSmoothClosedFiltration (Cycle.Support.cycleComponentι X.left x ≫ X.hom)
    (Stratification.Basic.singularLocusClosed (Cycle.Support.cycleComponentι X.left x ≫ X.hom)) k

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the reduced closure of
the scheme point `x`. Start with `S₀ = Z_sing` and obtain `S_{k+1}` by removing the smooth locus
of the reduced scheme on `S_k`. This is the image of `S_k` as a closed subset of the ambient
scheme `X`. -/
def Cycle.ComponentSingularClosedFiltration.cycleComponentSingularAmbientClosedFiltration (k : ℕ) : Closeds X.left :=
  ⟨Cycle.Support.cycleComponentι X.left x '' (Cycle.ComponentSingularClosedFiltration.cycleComponentSingularClosedFiltration X x k : Set _),
    (Cycle.Support.cycleComponentι X.left x).isClosedEmbedding.isClosedMap _
      (Cycle.ComponentSingularClosedFiltration.cycleComponentSingularClosedFiltration X x k).isClosed⟩

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the reduced closure of
the scheme point `x`. Start with `S₀ = Z_sing` and obtain `S_{k+1}` by removing the smooth locus
of the reduced scheme on `S_k`. This is the analytically closed subset `S_k(ℂ) ⊆ X(ℂ)`, formed
by taking complex points whose underlying scheme points lie in `S_k`. -/
def ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSingularAnalyticClosedFiltration (k : ℕ) : Closeds (ComplexPoint.Basic.ComplexSchemePoint X) :=
  ⟨ComplexPoint.Basic.Point.underlying ⁻¹' (Cycle.ComponentSingularClosedFiltration.cycleComponentSingularAmbientClosedFiltration X x k : Set X.left),
    (Cycle.ComponentSingularClosedFiltration.cycleComponentSingularAmbientClosedFiltration X x k).isClosed.preimage
      (ComplexPoint.Basic.ComplexSchemePoint.continuous_underlying_to_zariski X)⟩

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the reduced closure of
the scheme point `x`. This is the smooth locus `Z_reg` as a scheme over `ℂ`, with structure
morphism induced by its inclusion in `Z` and then in `X`. -/
abbrev ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver : Over (Spec ↧ℂ) :=
  Over.mk (((Cycle.Support.cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫
    Cycle.Support.cycleComponentι X.left x) ≫ X.hom)

instance ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver_locallyOfFiniteType :
    LocallyOfFiniteType (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothLocusOver X x).hom := by
  change LocallyOfFiniteType
    (((Cycle.Support.cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫
      Cycle.Support.cycleComponentι X.left x) ≫ X.hom)
  rw [Category.assoc]
  infer_instance

end

end OAI.AlgebraicGeometry
