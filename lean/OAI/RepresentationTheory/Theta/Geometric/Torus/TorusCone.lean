import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusImageCharts
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts

/-! # Torus Cone -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus.TorusCone.CM.Algebraization.Cone

noncomputable section

open Set

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

theorem projective_image_holomorphic_equations
    (Φ : Data.CM.ProjectivePeriodData) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)),
      Topology.IsClosedEmbedding f ∧
      ∀ i p, p ∈ range f → p ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
        AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt ((AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).symm ⁻¹' range f)
          (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i p) := by
  obtain ⟨n, f, hf, hlocal⟩ := TorusImageCharts.CM.Algebraization.ImageCharts.projective_period_torus_image_equations Φ
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
    (Φ : Data.CM.ProjectivePeriodData) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ)),
      Topology.IsClosedEmbedding f ∧ IsClosed (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) ∧
      (∀ v ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), v ≠ 0 →
        AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) v) ∧
      (AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.coordinateProjectionCenter n ∉ range f →
        IsProperMap (fun x : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.tailProjection n x) ∧
        ∀ y : Fin n → ℂ,
          {c : ℂ | Fin.cons c y ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)}.Finite) := by
  obtain ⟨n, f, hf, hlocal⟩ := projective_image_holomorphic_equations Φ
  exact ⟨n, f, hf, AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.isClosed_projectiveCone _ hf.isClosed_range,
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.holomorphicZeroSetAt_projectiveCone _ hlocal,
    fun hc => AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeCharts.Constructions.Cone.proper_finite_projectiveCone_projection _ hf.isClosed_range hc hlocal⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Torus.TorusCone.CM.Algebraization.Cone
