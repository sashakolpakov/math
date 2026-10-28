import OAI.AlgebraicGeometry.Cycles.Functoriality.ImageOpen

/-! # Boundary Containment -/

namespace OAI.AlgebraicGeometry.Cycles.Functoriality.BoundaryContainment.Construction

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

/-- Membership in the omitted support boundary is exactly failure of
membership in the chosen open before applying the closed inclusion. -/
theorem supportOpenBoundary_preimage {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Z.scheme.Opens) :
    Z.inclusion ⁻¹' (ImageOpen.Construction.supportOpenBoundary Z U : Set V.carrier) = (U : Set Z.scheme)ᶜ := by
  exact Set.preimage_image_eq _ Z.inclusion.isClosedEmbedding.injective

/-- A support's singular boundary lies in the complement of every
smooth open of the support. -/
theorem singularBoundary_subset_supportOpenBoundary {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Z.scheme.Opens) (hU : U ≤ Z.structureMap.smoothLocus) :
    CycleClass.Geometric.StratumDimension.supportSingularBoundary Z.1 V.structureMap ⊆ (ImageOpen.Construction.supportOpenBoundary Z U : Set V.carrier) := by
  rintro x ⟨z, hz, rfl⟩
  refine ⟨z, ?_, rfl⟩
  intro hzU
  exact hz (hU hzU)

/-- The ambient complement of the omitted support boundary is contained
in the canonical regular ambient open. -/
theorem boundaryComplement_subset_regularAmbient {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Z.scheme.Opens) (hU : U ≤ Z.structureMap.smoothLocus) :
    (TraceDetection.Construction.algebraicComplementOpen V (ImageOpen.Construction.supportOpenBoundary Z U) : Set V.analyticSpace) ⊆
      Z.regularAmbientOpen := by
  intro x hx hs
  exact hx (singularBoundary_subset_supportOpenBoundary Z U hU hs)

/-- A smooth inverse image of the chosen target open contains all source
support points whose ambient image avoids the target's omitted boundary. -/
theorem sourceSingularBoundary_maps_into_supportOpenBoundary
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p q : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) (T : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport Y q)
    (f : X.toOver ⟶ Y.toOver) (i : Z.scheme ⟶ T.scheme)
    (hi : i ≫ T.inclusion = Z.inclusion ≫ SupportMap.Construction.algebraicMap f)
    (U : T.scheme.Opens) (hU : i ⁻¹ᵁ U ≤ Z.structureMap.smoothLocus) :
    CycleClass.Geometric.StratumDimension.supportSingularBoundary Z.1 X.structureMap ⊆
      SupportMap.Construction.algebraicMap f ⁻¹' (ImageOpen.Construction.supportOpenBoundary T U : Set Y.carrier) := by
  rintro x ⟨z, hz, rfl⟩
  refine ⟨i z, ?_, ?_⟩
  · intro hzU
    exact hz (hU hzU)
  · exact congrArg (fun k : Z.scheme ⟶ Y.carrier => k z) hi

/-- On native complex points, the same algebraic containment ensures
that compact preimages avoid the source singular boundary. -/
theorem boundaryComplement_preimage_subset_regularAmbient
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p q : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) (T : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport Y q)
    (f : X.toOver ⟶ Y.toOver) (i : Z.scheme ⟶ T.scheme)
    (hi : i ≫ T.inclusion = Z.inclusion ≫ SupportMap.Construction.algebraicMap f)
    (U : T.scheme.Opens) (hU : i ⁻¹ᵁ U ≤ Z.structureMap.smoothLocus) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ⁻¹'
        (TraceDetection.Construction.algebraicComplementOpen Y (ImageOpen.Construction.supportOpenBoundary T U) : Set Y.analyticSpace) ⊆
      Z.regularAmbientOpen := by
  intro x hx hs
  have hb := sourceSingularBoundary_maps_into_supportOpenBoundary Z T f i hi U hU hs
  exact hx hb

/-- An analytic support point whose ambient image avoids the omitted
boundary belongs to the chosen support open. -/
theorem supportPoint_mem_open_of_boundaryComplement
    {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (U : Z.scheme.Opens) (x : Z.analyticSpace)
    (hx : Z.analyticInclusion x ∈ TraceDetection.Construction.algebraicComplementOpen V (ImageOpen.Construction.supportOpenBoundary Z U)) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ U := by
  by_contra hn
  exact hx ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x, hn, rfl⟩

end

end OAI.AlgebraicGeometry.Cycles.Functoriality.BoundaryContainment.Construction
