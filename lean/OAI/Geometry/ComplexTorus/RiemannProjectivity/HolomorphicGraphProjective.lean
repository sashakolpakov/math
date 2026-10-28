import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveVarietyCompactness

/-! # Holomorphic Graph Projective -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphProjective.Constructions.HolomorphicGraphEquations

noncomputable section

/-! # RiemannProjectivity: homogeneous polynomial equations for an arbitrary holomorphic graph -/

open Set _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold
open OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates
attribute [local instance] Classical.propDecidable

variable {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] {m n : ℕ}

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom] in
theorem graph_closed [CompactSpace (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (a : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)) [IsClosedImmersion a.left]
    (b : Y ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) [IsClosedImmersion b.left]
    (f : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) (hf : Continuous f) :
    Topology.IsClosedEmbedding (HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.graph a b f) := by
  apply (HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.graph_continuous a b f hf).isClosedEmbedding
  intro x y h
  have heq : (HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.embedding a x, HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.embedding b (f x)) = (HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.embedding a y, HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.embedding b (f y)) :=
    AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SegreAt.Constructions.Segre.segre_injective h
  exact (HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.embedding_closed a).injective (congrArg Prod.fst heq)

theorem projective_equations [CompactSpace (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [Nonempty (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    (a : X ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)) [IsClosedImmersion a.left]
    (b : Y ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) [IsClosedImmersion b.left]
    (f : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
    (hf : MDifferentiable (𝓘(ℂ, HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model X)) (𝓘(ℂ, HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model Y)) f) :
    ∃ (Q : Finset (MvPolynomial (Fin (m + 1) × Fin (n + 1)) ℂ))
      (degree : Q → ℕ) (hQ : ∀ q : Q, q.val.IsHomogeneous (degree q)),
      range (HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.graph a b f) = AlgebraicGeometry.Foundations.Scheme.ProjectiveZeroLocus.projectiveCommonZeroLocus (fun q : Q => q.val) degree hQ := by
  have hd := HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.graph_chart_data a b f hf
  have hc := graph_closed a b f hf.continuous
  have hpoly := ProjectiveManifoldFinite.Constructions.ProjectiveManifoldEquations.finite_homogeneous_equations
    (V := HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.model X) (M := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (ι := Fin (m + 1) × Fin (n + 1)) (HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.graph a b f) hc
  obtain ⟨Q, hQ, hcone⟩ := hpoly hd
  choose degree hdegree using fun q : Q => hQ q.val q.property
  refine ⟨Q, degree, hdegree, ?_⟩
  ext p
  have heq : p.rep ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range (HolomorphicGraphAt.Constructions.HolomorphicGraphCoordinates.graph a b f)) ↔
      ∀ q ∈ Q, MvPolynomial.eval p.rep q = 0 := by
    rw [hcone]
    rfl
  rw [AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.mem_projectiveCone_iff _ p.rep p.rep_nonzero, p.mk_rep] at heq
  rw [← p.mk_rep, AlgebraicGeometry.Foundations.Scheme.ProjectiveZeroLocus.mem_projectiveCommonZeroLocus_mk]
  simpa only [p.mk_rep, Subtype.forall] using heq

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicGraphProjective.Constructions.HolomorphicGraphEquations
