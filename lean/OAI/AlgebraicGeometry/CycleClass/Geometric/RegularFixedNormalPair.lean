import OAI.AlgebraicGeometry.ComplexPoints.Analytic.NormalCoordinatesDifferentiable
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexNormalAtlas

/-! # Regular Fixed Normal Pair -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric

noncomputable section

/-!
# Fixed normal coordinates for the regular support of an algebraic cycle

The regular support is a genuine closed complex immersion in the complement
of its singular boundary. Its proved codimension identifies the complement
in the immersion normal form with `Fin p → ℂ`. The resulting normal pairs,
their differentiability, and their open cover are consequences of this
geometry; no normal atlas is added as an assumption.
-/

open Set _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold _root_.Topology

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- The dimension difference used by the general complex-immersion
construction is the actual codimension of the cycle. -/
theorem DimensionCycles.DimensionCycleSupport.regularComplement_complexImmersionCodimension (Z : DimensionCycles.DimensionCycleSupport V p) :
    ComplexNormalAtlas.Cycles.complexImmersionCodimension Z.regularAnalyticModel V.analyticModel = p := by
  change Module.finrank ℂ V.analyticModel - Module.finrank ℂ Z.regularAnalyticModel = p
  rw [V.analyticModel_complex_finrank, Z.regularAnalyticModel_complex_finrank]
  have hd := Z.regularComplexDimension_add_codimension
  omega

/-- The actual regular-support immersion has the same normal model
`ℂ^p` at every point, by transporting its proved complement equivalence. -/
theorem DimensionCycles.DimensionCycleSupport.regularFixedComplementImmersion (Z : DimensionCycles.DimensionCycleSupport V p) :
    Manifold.IsImmersionOfComplement (Fin p → ℂ)
      𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, V.analyticModel) ω
      Z.regularComplementInclusion := fun x =>
  (Z.regularComplement_isImmersionAt x).isImmersionAtOfComplement_complement.trans_F
    (Z.regularComplementChartEquivFin x)

/-- A genuine normal pair for the whole regular support, with its normal
coordinate space fixed to the cycle's codimension. -/
def DimensionCycles.DimensionCycleSupport.regularFixedNormalPair (Z : DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ)
      Z.regularComplementInclusion x :=
  ComplexPoints.Analytic.NormalPairRecenter.normalPairOfImmersion (Z.regularFixedComplementImmersion x)
    Z.isClosedEmbedding_regularComplementInclusion.isEmbedding

/-- The coordinate map is the actual split, centered immersion chart. -/
theorem DimensionCycles.DimensionCycleSupport.regularFixedNormalPair_ambientChart (Z : DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    (Z.regularFixedNormalPair x).ambientChart =
      ComplexPoints.Analytic.NormalPairRecenter.immersionNormalCoordinates (Z.regularFixedComplementImmersion x) := rfl

/-- Both directions of each actual normal chart are complex differentiable. -/
theorem DimensionCycles.DimensionCycleSupport.regularFixedNormalPair_ambientChart_mdifferentiable
    (Z : DimensionCycles.DimensionCycleSupport V p) (x : Z.regularAnalyticSpace) :
    (Z.regularFixedNormalPair x).ambientChart.MDifferentiable
      𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ)) :=
  ComplexPoints.Analytic.NormalCoordinatesDifferentiable.normalPairOfImmersion_ambientChart_mdifferentiable
    (Z.regularFixedComplementImmersion x)
    Z.isClosedEmbedding_regularComplementInclusion.isEmbedding (by simp)

/-- In the actual normal neighborhood, the zero normal coordinate is
equivalent to membership in the original algebraic support. -/
theorem DimensionCycles.DimensionCycleSupport.regularFixedNormalPair_mem_support (Z : DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) (y : (Z.regularFixedNormalPair x).neighborhood) :
    (y.val : V.analyticSpace) ∈ Set.range Z.analyticInclusion ↔
      ((Z.regularFixedNormalPair x).homeomorph y).2.val = 0 := by
  change y.val ∈ Subtype.val ⁻¹' Set.range Z.analyticInclusion ↔ _
  rw [← Z.range_regularComplementInclusion]
  exact (Z.regularFixedNormalPair x).mem_range_iff y

/-- The actual support image is exactly the tangential ball times the
zero vector in `ℂ^p`. -/
theorem DimensionCycles.DimensionCycleSupport.regularFixedNormalPair_image_support (Z : DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    (Z.regularFixedNormalPair x).ambientChart ''
        ((Z.regularFixedNormalPair x).neighborhood ∩
          (Subtype.val ⁻¹' Set.range Z.analyticInclusion)) =
      Metric.ball (0 : Z.regularAnalyticModel) (Z.regularFixedNormalPair x).radius ×ˢ
        ({0} : Set (Fin p → ℂ)) := by
  rw [← Z.range_regularComplementInclusion]
  exact (Z.regularFixedNormalPair x).ambientChart_image_support

/-- The fixed-model normal pairs can be shrunk into any neighborhood
without changing their actual coordinate maps. -/
theorem DimensionCycles.DimensionCycleSupport.regularFixedNormalPair_cofinal (Z : DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) (U : Set Z.regularAmbientSpace)
    (hU : U ∈ 𝓝 (Z.regularComplementInclusion x)) :
    ∃ P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ)
        Z.regularComplementInclusion x,
      P.ambientChart = (Z.regularFixedNormalPair x).ambientChart ∧ P.neighborhood ⊆ U :=
  (Z.regularFixedNormalPair x).exists_subpair U hU

/-- The same cofinality holds after including the boundary complement
in the original projective variety. -/
theorem DimensionCycles.DimensionCycleSupport.regularFixedNormalPair_cofinal_ambient (Z : DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) (U : Set V.analyticSpace)
    (hU : U ∈ 𝓝 (Z.regularAnalyticToAmbient x)) :
    ∃ P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ)
        Z.regularComplementInclusion x,
      P.ambientChart = (Z.regularFixedNormalPair x).ambientChart ∧
        Subtype.val '' P.neighborhood ⊆ U := by
  have hpre : Subtype.val ⁻¹' U ∈ 𝓝 (Z.regularComplementInclusion x) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hU
  obtain ⟨P, he, hP⟩ := Z.regularFixedNormalPair_cofinal x (Subtype.val ⁻¹' U) hpre
  exact ⟨P, he, by rintro y ⟨z, hz, rfl⟩; exact hP hz⟩

/-- The genuine open ambient neighborhood of a fixed-model normal pair. -/
def DimensionCycles.DimensionCycleSupport.regularFixedNormalOpen (Z : DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) : Opens Z.regularAmbientSpace :=
  ⟨(Z.regularFixedNormalPair x).neighborhood,
    (Z.regularFixedNormalPair x).isOpen_neighborhood⟩

theorem DimensionCycles.DimensionCycleSupport.regularFixedNormalOpen_contains (Z : DimensionCycles.DimensionCycleSupport V p)
    (x : Z.regularAnalyticSpace) :
    Z.regularComplementInclusion x ∈ Z.regularFixedNormalOpen x :=
  (Z.regularFixedNormalPair x).point_mem_neighborhood

/-- Every point of the regular support lies in one of the proved normal
neighborhoods with the same normal coordinate space. -/
theorem DimensionCycles.DimensionCycleSupport.regularFixedNormalOpen_covers_support (Z : DimensionCycles.DimensionCycleSupport V p)
    (y : Z.regularAmbientSpace) (hy : (y : V.analyticSpace) ∈ Set.range Z.analyticInclusion) :
    ∃ x : Z.regularAnalyticSpace, y ∈ Z.regularFixedNormalOpen x := by
  have hr : y ∈ Set.range Z.regularComplementInclusion := by
    rw [Z.range_regularComplementInclusion]
    exact hy
  obtain ⟨x, rfl⟩ := hr
  exact ⟨x, Z.regularFixedNormalOpen_contains x⟩

/-- The fixed-model neighborhoods and the actual complement of the
support form an open cover of the whole boundary-complement manifold. -/
theorem DimensionCycles.DimensionCycleSupport.regularFixedNormalOpen_cover (Z : DimensionCycles.DimensionCycleSupport V p) :
    iSup Z.regularFixedNormalOpen ⊔
      EmbeddedSupportComplement.Cycles.embeddedSupportComplement Z.regularComplementInclusion
        Z.isClosedEmbedding_regularComplementInclusion = ⊤ := by
  apply top_unique
  intro y _
  by_cases hy : y ∈ Set.range Z.regularComplementInclusion
  · obtain ⟨x, rfl⟩ := hy
    exact Or.inl ((le_iSup Z.regularFixedNormalOpen x)
      (Z.regularFixedNormalOpen_contains x))
  · exact Or.inr hy

end

end OAI.AlgebraicGeometry.CycleClass.Geometric
