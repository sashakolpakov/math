import OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.Half
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.AxisInterval
import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantBoundaryRepresentatives

/-! # Half Chains -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.HalfChains

noncomputable section

/-! The two actual rational ray chains, their endpoints, and the full axis interval. -/

open _root_.CategoryTheory
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def axisHalfInclusion (b : Bool) : TopCat.of (Half.axisHalfLine b) ⟶ TopCat.of ℝ :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem axisHalfRaySimplex_face_zero (b : Bool) :
    (TopCat.toSSet.obj (TopCat.of (Half.axisHalfLine b))).δ 0 (Half.axisHalfRaySimplex b) =
      (TopCat.toSSetObj₀Equiv (X := TopCat.of (Half.axisHalfLine b))).symm (Half.axisHalfEndpoint b) := by
  apply ((TopCat.of (Half.axisHalfLine b)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  change (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace 0 t).weights 1 * (OrthantSphereEquator.orthantSign b : ℝ) = (OrthantSphereEquator.orthantSign b : ℝ)
  have h := OrthantSphereEquator.standardSimplexFace_succAbove (0 : Fin 2) t (0 : Fin 1)
  change (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace 0 t).weights 1 = t.weights 0 at h
  rw [h, PlaneHalfFaces.oneVertexSimplex_coordinate, one_mul]

theorem axisHalfRaySimplex_face_one (b : Bool) :
    (TopCat.toSSet.obj (TopCat.of (Half.axisHalfLine b))).δ 1 (Half.axisHalfRaySimplex b) =
      (TopCat.toSSetObj₀Equiv (X := TopCat.of (Half.axisHalfLine b))).symm (Half.axisHalfOrigin b) := by
  apply ((TopCat.of (Half.axisHalfLine b)).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  change (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace 1 t).weights 1 * (OrthantSphereEquator.orthantSign b : ℝ) = 0
  rw [OrthantSphereEquator.standardSimplexFace_omitted_zero, zero_mul]

def rationalAxisHalfRayChain (b : Bool) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (Half.axisHalfLine b))).X 1 :=
  AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℚ) (TopCat.toSSet.obj (TopCat.of (Half.axisHalfLine b))) (Half.axisHalfRaySimplex b)

theorem rationalAxisHalfRayChain_boundary (b : Bool) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (Half.axisHalfLine b))).d 1 0 (rationalAxisHalfRayChain b) =
      Singular.CrossBoundary.scalarPointChain ℚ (TopCat.of (Half.axisHalfLine b)) (Half.axisHalfEndpoint b) -
        Singular.CrossBoundary.scalarPointChain ℚ (TopCat.of (Half.axisHalfLine b)) (Half.axisHalfOrigin b) := by
  change (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℚ) (TopCat.toSSet.obj (TopCat.of (Half.axisHalfLine b)))).d 1 0
    (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℚ) (TopCat.toSSet.obj (TopCat.of (Half.axisHalfLine b))) (Half.axisHalfRaySimplex b)) = _
  rw [AlgebraicTopology.Kunneth.ComparisonLow.Construction.LowComparison.simplexChain_boundary_one, axisHalfRaySimplex_face_zero,
    axisHalfRaySimplex_face_one]
  rfl

theorem realAxisIntervalChain_split :
    Half.realAxisIntervalChain =
      AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (TopCat.of ℝ)) (Half.realAxisRaySimplex (fun _ => true)) -
        AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (TopCat.of ℝ)) (Half.realAxisRaySimplex (fun _ => false)) := by
  rw [Half.realAxisIntervalChain, OrthantBoundaryRepresentatives.sum_orthant_head_tail]
  simp only [Fintype.sum_unique]
  have hw (b : Bool) : OrthantSphereEquator.orthantWeight (Fin.cons b (default : Fin 0 → Bool)) = OrthantSphereEquator.orthantSign b := by
    rw [OrthantSphereEquator.orthantWeight_cons]
    simp [OrthantSphereEquator.orthantWeight]
  erw [hw, hw]
  change (-1 : ℤ) • _ + (1 : ℤ) • _ = _
  erw [neg_one_zsmul, one_zsmul, add_comm, sub_eq_add_neg]
  congr 2

theorem rationalSingularChainElement_simplex (X : TopCat.{0}) (n : ℕ)
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    Rational.ChainRepresentatives.rationalSingularChainElement X n (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) s) =
      AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℚ) (TopCat.toSSet.obj X) s :=
  CycleClass.Geometric.RationalSingularChains.Cycles.rationalSingularChainsIso_hom_one_tmul_simplex X n s

theorem rationalAxisIntervalChain_split :
    Rational.AxisInterval.rationalAxisIntervalChain =
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (axisHalfInclusion true)).f 1 (rationalAxisHalfRayChain true) -
        ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (axisHalfInclusion false)).f 1 (rationalAxisHalfRayChain false) := by
  rw [Rational.AxisInterval.rationalAxisIntervalChain, realAxisIntervalChain_split, Rational.ChainRepresentatives.rationalSingularChainElement_sub,
    rationalSingularChainElement_simplex, rationalSingularChainElement_simplex]
  change _ = ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (axisHalfInclusion true)).f 1
      (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℚ) (TopCat.toSSet.obj (TopCat.of (Half.axisHalfLine true))) (Half.axisHalfRaySimplex true)) -
    ((AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains ℚ).map (axisHalfInclusion false)).f 1
      (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℚ) (TopCat.toSSet.obj (TopCat.of (Half.axisHalfLine false))) (Half.axisHalfRaySimplex false))
  rw [AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains_map_simplex,
    AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.scalarChains_map_simplex]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.HalfChains
