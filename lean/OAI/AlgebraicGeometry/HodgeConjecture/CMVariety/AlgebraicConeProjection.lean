import OAI.Geometry.ComplexTorus.RiemannProjectivity.GenericProjectionOn
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicCone

/-! # Algebraic Cone Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicConeProjection.CM.Abelian.Algebraization.ConeProjection

noncomputable section

open Set

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

/-- Every holomorphically parametrized image admits the required cone projection. -/
theorem projection_of_period_embedding {n : ℕ}
    (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData)
    (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ))
    (hf : Continuous f)
    (hd : ∀ (z : Φ.space) (i : Fin (n + 1)),
      Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (f (QuotientAddGroup.mk z)) →
        DifferentiableAt ℂ
          (fun w => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f (QuotientAddGroup.mk w))) z) :
    ∃ L : (Fin (n + 1) → ℂ) →L[ℂ]
        (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ),
      ∀ v ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), L v = 0 → v = 0 := by
  let g : Φ.space → Projectivization ℂ (Fin (n + 1) → ℂ) :=
    fun z => f (QuotientAddGroup.mk z)
  let U : Fin (n + 1) → Set (Φ.space) :=
    fun i => g ⁻¹' (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source
  let r : Fin (n + 1) → Φ.space → Fin n → ℂ :=
    fun i z => ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g z)
  have hg : Continuous g := hf.comp QuotientAddGroup.continuous_mk
  have hU : ∀ i, IsOpen (U i) := fun i => (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).open_source.preimage hg
  have hr : ∀ i, DifferentiableOn ℂ (r i) (U i) :=
    fun i z hz => (hd z i hz).differentiableWithinAt
  apply Geometry.ComplexTorus.RiemannProjectivity.GenericProjectionOn.Constructions.GenericProjection.exists_projection_avoiding (Nat.lt_succ_self _) U r hU hr
    (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f))
  intro v hv hv0
  obtain ⟨t, ht⟩ := hv hv0
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk_surjective t
  obtain ⟨i, hi⟩ := ComplexPoints.Analytic.ProjectiveCharts.exists_mem_projectiveFinChart_source (Projectivization.mk ℂ v hv0)
  have hgz : g z = Projectivization.mk ℂ v hv0 := by simp only [g, hz, ht]
  refine ⟨i, z, ?_, (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff i v hv0).mp hi, ?_⟩
  · change g z ∈ (ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source
    rwa [hgz]
  · intro j
    change v (i.succAbove j) / v i = ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g z) j
    rw [hgz, ← ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.dehomogenize_eq_projectiveChart i v hv0]
    rfl

/-- The CM projective period cone has a proper linear projection to complex
dimension `dim(T) + 1`, together with a global quantitative norm estimate. -/
theorem proper_period_cone_projection
    (Φ : ProjectiveTorusData.CM.Abelian.ProjectivePeriodData) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ))
      (L : (Fin (n + 1) → ℂ) →L[ℂ]
        (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ)),
      Topology.IsClosedEmbedding f ∧
      (∀ v ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), L v = 0 → v = 0) ∧
      IsProperMap (fun v : ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => L v) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ v ∈ ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), ‖v‖ ≤ C * ‖L v‖ := by
  obtain ⟨n, f, hf, hd⟩ := AlgebraizationRoot.CM.Abelian.Algebraization.projective_period_torus_all_charts Φ
  obtain ⟨L, hL⟩ := projection_of_period_embedding Φ f hf.continuous
    (fun z i hi => (hd z i hi).1)
  have hc := ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.isClosed_projectiveCone (range f) hf.isClosed_range
  refine ⟨n, f, L, hf, hL, ?_, ?_⟩
  · exact ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.isProperMap_projection hc (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone (range f)) L hL
  · exact ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.norm_le_projection hc (ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone (range f)) L hL

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicConeProjection.CM.Abelian.Algebraization.ConeProjection
