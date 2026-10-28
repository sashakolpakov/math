import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicTopology.DeRham.Comparison.DuffyFaces
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts
import OAI.AlgebraicGeometry.CycleClass.Geometric.ClosedBall

/-! # Local Simplex -/

namespace OAI.AlgebraicTopology.FundamentalClass.LocalSimplex.IntegrationGeometry

noncomputable section

/-! Integration: the positively ordered affine simplex defines an actual local cycle.
Its vertices are `-b, e₁-b,..., e_d-b`, where every coordinate of `b` is
`1/(d+1)`. The origin is its barycenter. This fixes the sign geometrically,
without choosing an arbitrary generator of a rank-one homology group. -/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false

def positiveSimplex (d : ℕ) :
    C(Convexity.StdSimplex ℝ (Fin (d + 1)), Fin d → ℝ) where
  toFun t i := t.weights i.succ - ((d + 1 : ℕ) : ℝ)⁻¹
  continuous_toFun := continuous_pi fun i =>
    (Convexity.StdSimplex.continuous_weights_apply ℝ i.succ).sub continuous_const

theorem positiveSimplex_zero_coordinates (d : ℕ)
    (t : Convexity.StdSimplex ℝ (Fin (d + 1))) (ht : positiveSimplex d t = 0)
    (i : Fin (d + 1)) : t.weights i = ((d + 1 : ℕ) : ℝ)⁻¹ := by
  have hs (j : Fin d) : t.weights j.succ = ((d + 1 : ℕ) : ℝ)⁻¹ := by
    have h := congrFun ht j
    exact sub_eq_zero.mp h
  refine Fin.cases ?_ hs i
  have hsum := t.total_of_fintype
  rw [Fin.sum_univ_succ] at hsum
  simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hd : (((d + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hmul := mul_inv_cancel₀ hd
  push_cast at hmul
  push_cast at hsum ⊢
  nlinarith

theorem positiveSimplex_face_ne_zero (d : ℕ) (i : Fin (d + 2))
    (t : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    positiveSimplex (d + 1) (Convexity.StdSimplex.map i.succAbove t) ≠ 0 := by
  intro h
  have hi := positiveSimplex_zero_coordinates (d + 1) _ h i
  rw [DeRham.Comparison.DuffyFaces.Duffy.simplexFace_eq_insertNth, Fin.insertNth_apply_same] at hi
  have : (((d + 1 + 1 : ℕ) : ℝ))⁻¹ ≠ 0 := inv_ne_zero (by positivity)
  exact this hi.symm

def positiveSingularSimplex (d : ℕ) :
    Cohomology.Singular.Basic.singularSimplices (TopCat.of (Fin d → ℝ)) d :=
  (TopCat.toSSetObjEquiv (TopCat.of (Fin d → ℝ)) (op ⦋d⦌)).symm
    (positiveSimplex d)

/-- A simplex whose image is in the subspace projects to zero in relative chains. -/
theorem relativeProjection_simplex_zero {X : TopCat.{0}} (A : Set X) {d : ℕ}
    (s : Cohomology.Singular.Basic.singularSimplices X d)
    (hs : ∀ t, X.toSSetObjEquiv (op ⦋d⦌) s t ∈ A) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f d
      (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) s) = 0 := by
  let lift : C(Convexity.StdSimplex ℝ (Fin (d + 1)), A) :=
    ⟨fun t => ⟨X.toSSetObjEquiv (op ⦋d⦌) s t, hs t⟩,
      (X.toSSetObjEquiv (op ⦋d⦌) s).continuous.subtype_mk _⟩
  let t := (TopCat.toSSetObjEquiv (TopCat.of A) (op ⦋d⦌)).symm lift
  have ht : (TopCat.toSSet.map (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A)).app (op ⦋d⦌) t = s := by
    apply (X.toSSetObjEquiv (op ⦋d⦌)).injective
    rfl
  have hmap : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A).f d
      (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (TopCat.of A)) t) =
      Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) s := by
    change (Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℤ)
      (TopCat.toSSet.map (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A))).f d _ = _
    rw [Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap_simplex, ht]
  rw [← hmap]
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion_projection X A) d)
    (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (TopCat.of A)) t)

def positiveLocalChain (d : ℕ) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of (Fin d → ℝ)) ({0}ᶜ : Set (Fin d → ℝ))).X d :=
  (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of (Fin d → ℝ)) {0}ᶜ).f d
    (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (TopCat.of (Fin d → ℝ)))
      (positiveSingularSimplex d))

theorem positiveLocalChain_cycle (d : ℕ) :
    positiveLocalChain d ∈ Cohomology.Singular.ChainRepresentatives.chainCycles
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of (Fin d → ℝ)) ({0}ᶜ : Set (Fin d → ℝ))) d := by
  cases d with
  | zero => exact Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero _ _
  | succ d =>
    rw [Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ]
    let X := TopCat.of (Fin (d + 1) → ℝ)
    let π := AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X ({0}ᶜ : Set X)
    change (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X {0}ᶜ).d (d + 1) d
      (π.f (d + 1) (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X)
        (positiveSingularSimplex (d + 1)))) = 0
    have hcomm := ConcreteCategory.congr_hom (π.comm (d + 1) d).symm
      (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) (positiveSingularSimplex (d + 1)))
    change π.f d ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℤ) X).d (d + 1) d
      (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) (positiveSingularSimplex (d + 1)))) =
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X {0}ᶜ).d (d + 1) d
        (π.f (d + 1) (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X)
          (positiveSingularSimplex (d + 1)))) at hcomm
    rw [← hcomm]
    change π.f d ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℤ) X).d (d + 1) d
      (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) (positiveSingularSimplex (d + 1)))) = 0
    rw [Cohomology.Singular.ChainDual.simplexChain_boundary, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_zsmul]
    have hi : π.f d (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X)
        ((TopCat.toSSet.obj X).δ i (positiveSingularSimplex (d + 1)))) = 0 := by
      apply relativeProjection_simplex_zero
      intro t
      exact positiveSimplex_face_ne_zero d i t
    rw [hi]
    exact zsmul_zero _

/-- The actual local integral class of the positively ordered affine simplex. -/
def positiveLocalClass (d : ℕ) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin d → ℝ)) 0 d :=
  Cohomology.Singular.ChainRepresentatives.chainClass _ d ⟨positiveLocalChain d, positiveLocalChain_cycle d⟩

end

end OAI.AlgebraicTopology.FundamentalClass.LocalSimplex.IntegrationGeometry
