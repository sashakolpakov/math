import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PointFiberLinearForms
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.FiniteProjective

/-! # Fiber Equations -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.FiberEquations

noncomputable section

/-! Equations for fibers of the actual glued projective projection. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PointFiberLinearForms

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
  (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
  (h : ∀ x : X.carrier, ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal)

theorem homogeneous_mem (x : X.carrier) (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1) :
    a.val ∈ (FiniteProjective.FromForms.map X m L h x).asHomogeneousIdeal ↔
      FiniteProjective.FromForms.coordinates X m L a.val ∈ (X.embedding x).asHomogeneousIdeal := by
  have he := Projective.ProjectionRestriction.preimage_basicOpen
    (FiniteProjective.FromForms.coordinates X m L) X.embedding
    (FiniteProjective.FromForms.in_domain X m L h) a.val a.property Nat.zero_lt_one
  have he' := (congrArg (fun U : X.carrier.Opens => x ∈ U) he).to_iff
  exact not_iff_not.mp he'

def equation (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X.carrier) (hp : p ≫ X.structureMap = 𝟙 _)
    (i a : Fin (m + 1)) : Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1 :=
  PointFiberLinearForms.value X p hp (L i) • ⟨MvPolynomial.X a, Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous m a⟩ -
    PointFiberLinearForms.value X p hp (L a) • ⟨MvPolynomial.X i, Foundations.Scheme.ProjectiveChartToPolynomial.projectiveVariable_homogeneous m i⟩

theorem equation_pull (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X.carrier) (hp : p ≫ X.structureMap = 𝟙 _)
    (i a : Fin (m + 1)) :
    FiniteProjective.FromForms.coordinates X m L (equation X m L p hp i a).val =
      (PointFiberLinearForms.cross X p hp (L i) (L a)).val := by
  change FiniteProjective.FromForms.coordinates X m L
    (PointFiberLinearForms.value X p hp (L i) • MvPolynomial.X a - PointFiberLinearForms.value X p hp (L a) • MvPolynomial.X i) =
    PointFiberLinearForms.value X p hp (L i) • (L a).val - PointFiberLinearForms.value X p hp (L a) • (L i).val
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, map_sub, map_mul,
    FiniteProjective.FromForms.constants, FiniteProjective.FromForms.coordinate]

theorem fiber_equations (p : Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X.carrier) (hp : p ≫ X.structureMap = 𝟙 _)
    (i : Fin (m + 1)) (y : X.carrier)
    (hy : FiniteProjective.FromForms.map X m L h y =
      FiniteProjective.FromForms.map X m L h (p (IsLocalRing.closedPoint ℂ))) :
    ∀ a, (PointFiberLinearForms.cross X p hp (L i) (L a)).val ∈ (X.embedding y).asHomogeneousIdeal := by
  intro a
  have hx : (equation X m L p hp i a).val ∈
      (FiniteProjective.FromForms.map X m L h (p (IsLocalRing.closedPoint ℂ))).asHomogeneousIdeal := by
    apply (homogeneous_mem X m L h _ _).mpr
    rw [equation_pull]
    exact PointFiberLinearForms.cross_vanishes X p hp (L i) (L a)
  have hy' : (equation X m L p hp i a).val ∈
      (FiniteProjective.FromForms.map X m L h y).asHomogeneousIdeal := hy ▸ hx
  have he := (homogeneous_mem X m L h y _).mp hy'
  rwa [equation_pull] at he

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.FiberEquations
