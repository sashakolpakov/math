import OAI.AlgebraicTopology.DeRham.Comparison.CycleIsomorphismExtension
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSchemeDiffeomorph
import OAI.Topology.Euclidean.OpenCoordinateTransport

/-! # Cycle Isomorphism Diffeomorph -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.CycleIsomorphismDiffeomorph.DimensionCycleSupport

noncomputable section

/-!
# The actual analytic isomorphism on regular ambient spaces

An algebraic isomorphism restricts to a complex diffeomorphism between the
complements of the corresponding singular boundaries. Its function is the
literal subspace map used in the relative-cohomology naturality square, and
it takes the actual regular support image onto the transported support image.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped ContDiff _root_.Manifold

variable {V W : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- Restrict the native analytic isomorphism to the actual singular-boundary complements. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (r : ℕ∞ω) :
    Diffeomorph (𝓘(ℂ, V.analyticModel)) (𝓘(ℂ, W.analyticModel))
      Z.regularAmbientSpace (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularAmbientSpace r := by
  let : IsIntegral V.toOver.left := V.property
  let : Smooth V.toOver.hom := V.presentation.smooth
  let : IsIntegral W.toOver.left := W.property
  let : Smooth W.toOver.hom := W.presentation.smooth
  exact Topology.Euclidean.OpenCoordinateTransport.Globalization.restrictDiffeomorph (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSchemeDiffeomorph.nativeSchemeDiffeomorph e r)
    Z.regularAmbientOpen (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularAmbientOpen
    (fun x => by
      change x ∉ Z.analyticSingularBoundary ↔
        x ∉ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom ⁻¹'
          (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).analyticSingularBoundary
      rw [AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.analyticSingularBoundary_preimage_iso])

@[simp]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso_apply (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (r : ℕ∞ω) (x : Z.regularAmbientSpace) :
    (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso e Z r x).val =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom x.val := rfl

@[simp]
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso_symm_apply (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (r : ℕ∞ω)
    (y : (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularAmbientSpace) :
    ((AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso e Z r).symm y).val =
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.inv y.val := rfl

/-- The analytic diffeomorphism has exactly the function used in the relative-pair map. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso_eq_subspaceMap (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (r : ℕ∞ω) :
    ⇑(AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso e Z r) =
      ⇑(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceMap (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map e.hom)
        (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.iso_mapsTo_boundaryComplement e Z)) := by
  funext x
  rfl

/-- Forgetting smoothness gives the literal continuous subspace morphism. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso_toHom (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (r : ℕ∞ω) :
    TopCat.ofHom ⟨AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso e Z r,
        (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso e Z r).continuous⟩ =
      AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceMap (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map e.hom)
        (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.iso_mapsTo_boundaryComplement e Z) := by
  ext x
  rfl

/-- The restricted diffeomorphism preserves and reflects the actual regular support image. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso_mem_range (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (r : ℕ∞ω) (x : Z.regularAmbientSpace) :
    AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso e Z r x ∈
        Set.range (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularComplementInclusion ↔
      x ∈ Set.range Z.regularComplementInclusion := by
  rw [AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.range_regularComplementInclusion, AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.range_regularComplementInclusion]
  change x.val ∈ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map e.hom ⁻¹'
      Set.range (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).analyticInclusion ↔
    x.val ∈ Set.range Z.analyticInclusion
  rw [AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.analyticSupport_preimage_iso]

/-- Its image of the regular support is the entire transported regular support. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso_image_range (e : V.toOver ≅ W.toOver)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (r : ℕ∞ω) :
    AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso e Z r '' Set.range Z.regularComplementInclusion =
      Set.range (AlgebraicGeometry.CycleClass.Geometric.DimensionIsomorphism.dimensionCycleSupportIsoEquiv e p Z).regularComplementInclusion := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso_mem_range e Z r x).mpr hx
  · intro hy
    refine ⟨(AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso e Z r).symm y, ?_,
      (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso e Z r).apply_symm_apply y⟩
    apply (AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularAmbientDiffeomorphOfIso_mem_range e Z r _).mp
    simpa only [Diffeomorph.apply_symm_apply] using hy

end

end OAI.AlgebraicTopology.DeRham.Comparison.CycleIsomorphismDiffeomorph.DimensionCycleSupport
