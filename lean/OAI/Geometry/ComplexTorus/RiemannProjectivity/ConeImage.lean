import OAI.Geometry.ComplexTorus.RiemannProjectivity.ImageChartsIn
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts

/-! # Cone Image -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeImage.Constructions.Cone

noncomputable section

/-!
# RiemannProjectivity: projective cone of the realized CM torus

The proved local equations of the entire torus image feed the existing cone
theorems. This gives a closed complex cone, genuine holomorphic equations
away from its vertex, and proper finite coordinate projections whenever
their center avoids the image. No algebraicity of the cone is assumed.
-/

open Set

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E]

theorem projective_image_holomorphic_equations
    (hRiemannProjectivity : RiemannProjectivity.Fin.Constructions.RiemannProjectivityInput) (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)),
      Topology.IsClosedEmbedding f ∧
      ∀ i p, p ∈ range f → p ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
        AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt ((AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).symm ⁻¹' range f)
          (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i p) := by
  obtain ⟨n, f, hf, hlocal⟩ := ImageChartsIn.Constructions.ImageCharts.projective_period_torus_image_equations hRiemannProjectivity Φ
  refine ⟨n, f, hf, ?_⟩
  rintro i p ⟨t, rfl⟩ hi
  obtain ⟨k, O, g, hO, ht, hg, heq⟩ := hlocal t i hi
  refine ⟨O, hO, ht, k, (fun j y => g y j),
    (fun j => differentiableOn_pi.mp hg j), ?_⟩
  intro y hy
  change (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).symm y ∈ range f ↔ ∀ j, g y j = 0
  rw [← heq y hy]
  exact funext_iff

/-- The constructed cone is locally holomorphic at every nonzero point,
with the actual closed projective torus as its projectivization. -/
theorem period_cone_holomorphic
    (hRiemannProjectivity : RiemannProjectivity.Fin.Constructions.RiemannProjectivityInput) (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)),
      Topology.IsClosedEmbedding f ∧ IsClosed (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) ∧
      (∀ v ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), v ≠ 0 →
        AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) v) ∧
      (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.coordinateProjectionCenter n ∉ range f →
        IsProperMap (fun x : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.tailProjection n x) ∧
        ∀ y : Fin n → ℂ,
          {c : ℂ | Fin.cons c y ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)}.Finite) := by
  obtain ⟨n, f, hf, hlocal⟩ := projective_image_holomorphic_equations hRiemannProjectivity Φ
  exact ⟨n, f, hf, AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.isClosed_projectiveCone _ hf.isClosed_range,
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.holomorphicZeroSetAt_projectiveCone _ hlocal,
    fun hc => AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.proper_finite_projectiveCone_projection _ hf.isClosed_range hc hlocal⟩

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeImage.Constructions.Cone
