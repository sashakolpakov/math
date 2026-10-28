import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusRegularCone
import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusCone
import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusFiniteConeFibers
import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusConePolynomialEquations
import OAI.Geometry.ComplexTorus.RiemannProjectivity.AnalyticCone
import OAI.RepresentationTheory.Theta.Geometric.Torus.TorusConeSurjectivity

/-! # Torus Period Coordinate Equations -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus.TorusPeriodCoordinateEquations.CM.Algebraization.PeriodCoordinateEquations

noncomputable section

open Set _root_.Polynomial _root_.Metric

def HasLocalMonicEquation {d : ℕ} (S : Set ((Fin d → ℂ) × ℂ))
    (x : Fin d → ℂ) (z₀ : ℂ) : Prop :=
  ∃ (R : ℝ) (k : ℕ) (U : Set (Fin d → ℂ))
      (P : (Fin d → ℂ) → ℂ[X]) (c : (Fin d → ℂ) → ℂ),
    0 < R ∧ IsOpen U ∧ x ∈ U ∧ DifferentiableOn ℂ c U ∧
    U ⊆ closure {y | y ∈ U ∧ c y ≠ 0} ∧
    (∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) U) ∧
    (∀ y, (P y).Monic ∧ (P y).natDegree = k) ∧
    (∀ y ∈ U, ∀ z, (P y).eval z = 0 → (y, z) ∈ S) ∧
    (∀ y ∈ U, c y ≠ 0 → (P y).Separable) ∧
    ∀ y ∈ U, ∀ z ∈ ball z₀ R, (y, z) ∈ S ↔ (P y).eval z = 0

theorem period_coordinate_equations (Φ : Data.CM.ProjectivePeriodData) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ))
      (L : (Fin (n + 1) → ℂ) →L[ℂ]
        (Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ)),
      Topology.IsClosedEmbedding f ∧
      IsProperMap (fun v : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => L v) ∧
      Function.Surjective (fun v : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => L v) ∧
      (∀ y, {v : Fin (n + 1) → ℂ | v ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) ∧ L v = y}.Finite) ∧
      ∀ l : (Fin (n + 1) → ℂ) →L[ℂ] ℂ, Function.Surjective (L.prod l) →
        ∀ (x : Fin (Module.finrank ℂ (Φ.space) + 1) → ℂ) (z₀ : ℂ),
          (x, z₀) ∈ (fun v => (L v, l v)) '' AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) → x ≠ 0 →
          HasLocalMonicEquation ((fun v => (L v, l v)) '' AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) x z₀ := by
  obtain ⟨n, f, L, hf, hd, hker, hp, hi⟩ :=
    TorusRegularCone.CM.Algebraization.RegularCone.proper_period_cone_projection_with_interior_and_immersions Φ
  have hclosed := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.isClosed_projectiveCone (range f) hf.isClosed_range
  have hcone := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone (range f)
  have hlocal := TorusFiniteConeFibers.CM.Algebraization.FiniteConeFibers.cone_holomorphic_of_period_embedding Φ f hf hd
  have hfinite := TorusFiniteConeFibers.CM.Algebraization.FiniteConeFibers.finite_proper_cone_fiber L hp hker hlocal
  refine ⟨n, f, L, hf, hp,
    TorusConeSurjectivity.CM.Algebraization.ConeSurjectivity.surjective_cone_projection L hclosed hcone hker hlocal hi,
    hfinite, ?_⟩
  intro l hl x z₀ hx hx0
  have hpairker : ∀ v ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), (L.prod l) v = 0 → v = 0 := by
    intro v hv hzero
    exact hker v hv (congrArg Prod.fst hzero)
  have hpairproper := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.isProperMap_projection hclosed hcone (L.prod l) hpairker
  have hpairclosed : IsClosed ((fun v => (L v, l v)) '' AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) := by
    have h := hpairproper.isClosedMap.isClosed_range
    convert! h using 1
    ext u
    exact ⟨fun ⟨v, hv, he⟩ => ⟨⟨v, hv⟩, he⟩,
      fun ⟨v, he⟩ => ⟨v, v.property, he⟩⟩
  have hpairlocal := Geometry.ComplexTorus.RiemannProjectivity.AnalyticCone.Constructions.AnalyticConeImage.linear_projection (L.prod l) hl hclosed hcone
    hpairker hlocal (x, z₀) hx (fun hzero => hx0 (congrArg Prod.fst hzero))
  exact TorusConePolynomialEquations.CM.Algebraization.ConePolynomialEquations.local_equation_of_coordinate_image Φ f hf.isEmbedding
    (fun z i hi => (hd z i hi).1) L hfinite l hpairclosed hx0 hpairlocal

end

end OAI.RepresentationTheory.Theta.Geometric.Torus.TorusPeriodCoordinateEquations.CM.Algebraization.PeriodCoordinateEquations
