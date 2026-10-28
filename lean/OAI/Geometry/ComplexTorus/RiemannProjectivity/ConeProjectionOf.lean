import OAI.Geometry.ComplexTorus.RiemannProjectivity.GenericProjectionOn
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeImage

/-! # Cone Projection Of -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeProjectionOf.Constructions.ConeProjection

noncomputable section

/-!
# RiemannProjectivity: a proper projection of the actual period cone

The actual holomorphic projective parametrization supplies the incidence
charts. The projection target has one more complex dimension than the torus,
and its kernel meets the cone only at zero. Compactness then gives a global
norm estimate and properness of the restricted projection.
-/

open Set

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E]

/-- Every holomorphically parametrized image admits the required cone projection. -/
theorem projection_of_period_embedding {n : ℕ}
    (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ))
    (hf : Continuous f)
    (hd : ∀ (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) (i : Fin (n + 1)),
      AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f (QuotientAddGroup.mk z)) →
        DifferentiableAt ℂ
          (fun w => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z) :
    ∃ L : (Fin (n + 1) → ℂ) →L[ℂ]
        (Fin (Module.finrank ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) + 1) → ℂ),
      ∀ v ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), L v = 0 → v = 0 := by
  let g : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → Projectivization ℂ (Fin (n + 1) → ℂ) :=
    fun z => f (QuotientAddGroup.mk z)
  let U : Fin (n + 1) → Set (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) :=
    fun i => g ⁻¹' (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source
  let r : Fin (n + 1) → AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E → Fin n → ℂ :=
    fun i z => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g z)
  have hg : Continuous g := hf.comp QuotientAddGroup.continuous_mk
  have hU : ∀ i, IsOpen (U i) := fun i => (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).open_source.preimage hg
  have hr : ∀ i, DifferentiableOn ℂ (r i) (U i) :=
    fun i z hz => (hd z i hz).differentiableWithinAt
  apply GenericProjectionOn.Constructions.GenericProjection.exists_projection_avoiding (Nat.lt_succ_self _) U r hU hr
    (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))
  intro v hv hv0
  obtain ⟨t, ht⟩ := hv hv0
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk_surjective t
  obtain ⟨i, hi⟩ := AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.exists_mem_projectiveFinChart_source (Projectivization.mk ℂ v hv0)
  have hgz : g z = Projectivization.mk ℂ v hv0 := by simp only [g, hz, ht]
  refine ⟨i, z, ?_, (AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff i v hv0).mp hi, ?_⟩
  · change g z ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source
    rwa [hgz]
  · intro j
    change v (i.succAbove j) / v i = AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g z) j
    rw [hgz, ← AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize_eq_projectiveChart i v hv0]
    rfl

/-- The CM projective period cone has a proper linear projection to complex
dimension `dim(T) + 1`, together with a global quantitative norm estimate. -/
theorem proper_period_cone_projection
    (hRiemannProjectivity : RiemannProjectivity.Fin.Constructions.RiemannProjectivityInput) (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ))
      (L : (Fin (n + 1) → ℂ) →L[ℂ]
        (Fin (Module.finrank ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) + 1) → ℂ)),
      Topology.IsClosedEmbedding f ∧
      (∀ v ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), L v = 0 → v = 0) ∧
      IsProperMap (fun v : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => L v) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ v ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), ‖v‖ ≤ C * ‖L v‖ := by
  obtain ⟨n, f, hf, hd⟩ := RiemannProjectivity.Fin.Constructions.projective_period_torus_all_charts hRiemannProjectivity Φ
  obtain ⟨L, hL⟩ := projection_of_period_embedding Φ f hf.continuous
    (fun z i hi => (hd z i hi).1)
  have hc := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.isClosed_projectiveCone (range f) hf.isClosed_range
  refine ⟨n, f, L, hf, hL, ?_, ?_⟩
  · exact AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.isProperMap_projection hc (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone (range f)) L hL
  · exact AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.norm_le_projection hc (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone (range f)) L hL

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeProjectionOf.Constructions.ConeProjection
