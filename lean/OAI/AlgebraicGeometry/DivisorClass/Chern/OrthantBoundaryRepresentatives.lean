import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantSphereEquator
import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantHemisphereFaces
import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantWeightedBoundary
import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantSphereCycle

/-! # Orthant Boundary Representatives -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantBoundaryRepresentatives

noncomputable section

section

/-! Actual hemisphere and equator chains for the sphere connecting map. -/

open _root_.CategoryTheory
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

abbrev orthantSphereOverlap (n : ℕ) : TopCat.{0} := TopCat.of
  ↥(CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)) ∩ CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)))
abbrev orthantFirstChart (n : ℕ) : TopCat.{0} := TopCat.of (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)))
abbrev orthantSecondChart (n : ℕ) : TopCat.{0} := TopCat.of (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1)))

def orthantOverlapFirstInclusion (n : ℕ) : orthantSphereOverlap n ⟶ orthantFirstChart n :=
  CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1)) Set.inter_subset_left
def orthantOverlapSecondInclusion (n : ℕ) : orthantSphereOverlap n ⟶ orthantSecondChart n :=
  CycleClass.Geometric.SmallMayerVietoris.Cycles.subsetInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1)) Set.inter_subset_right

theorem integralSimplexChain_map {X Y : TopCat.{0}} (f : X ⟶ Y) {n : ℕ}
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f).f n (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) s) =
      AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj Y) ((TopCat.toSSet.map f).app _ s) :=
  ConcreteCategory.congr_hom (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj X)
    (TopCat.toSSet.obj Y) (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ) s) 1

def orthantEquatorOverlapSimplex (n : ℕ) (η : Fin (n + 1) → Bool) :
    (TopCat.toSSet.obj (orthantSphereOverlap n)) _⦋n⦌ :=
  (TopCat.toSSet.map (OrthantSphereEquator.orderedEquatorOverlap n)).app _ (OrthantSphereEquator.orthantSphereSimplex n η)

theorem orthantFirstChartSimplex_face_zero (n : ℕ) (η : Fin (n + 1) → Bool) :
    (TopCat.toSSet.obj (orthantFirstChart n)).δ 0 (OrthantHemisphereFaces.orthantFirstChartSimplex n η) =
      (TopCat.toSSet.map (orthantOverlapFirstInclusion n)).app _ (orthantEquatorOverlapSimplex n η) := by
  apply ((orthantFirstChart n).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  rw [TopCat.toSSetObjEquiv_δ_apply]
  apply Subtype.ext
  exact OrthantSphereEquator.orthantSphereMap_face_zero n false η t

theorem orthantSecondChartSimplex_face_zero (n : ℕ) (η : Fin (n + 1) → Bool) :
    (TopCat.toSSet.obj (orthantSecondChart n)).δ 0 (OrthantHemisphereFaces.orthantSecondChartSimplex n η) =
      (TopCat.toSSet.map (orthantOverlapSecondInclusion n)).app _ (orthantEquatorOverlapSimplex n η) := by
  apply ((orthantSecondChart n).toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  rw [TopCat.toSSetObjEquiv_δ_apply]
  apply Subtype.ext
  exact OrthantSphereEquator.orthantSphereMap_face_zero n true η t

def orthantEquatorChain (n : ℕ) : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (orthantSphereOverlap n)).X n :=
  ∑ η : Fin (n + 1) → Bool, OrthantSphereEquator.orthantWeight η •
    AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (orthantSphereOverlap n)) (orthantEquatorOverlapSimplex n η)

def orthantFirstHemisphereChain (n : ℕ) : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (orthantFirstChart n)).X (n + 1) :=
  -(∑ η : Fin (n + 1) → Bool, OrthantSphereEquator.orthantWeight η •
    AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (orthantFirstChart n)) (OrthantHemisphereFaces.orthantFirstChartSimplex n η))

def orthantSecondHemisphereChain (n : ℕ) : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (orthantSecondChart n)).X (n + 1) :=
  ∑ η : Fin (n + 1) → Bool, OrthantSphereEquator.orthantWeight η •
    AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (orthantSecondChart n)) (OrthantHemisphereFaces.orthantSecondChartSimplex n η)

theorem orthantFirstHemisphereChain_boundary (n : ℕ) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (orthantFirstChart n)).d (n + 1) n (orthantFirstHemisphereChain n) =
      -(CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (orthantOverlapFirstInclusion n)).f n (orthantEquatorChain n) := by
  unfold orthantFirstHemisphereChain
  rw [map_neg]
  congr 1
  change (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) (TopCat.toSSet.obj (orthantFirstChart n))).d (n + 1) n _ = _
  rw [OrthantWeightedBoundary.orthantWeighted_boundary_first _ n _ (OrthantHemisphereFaces.orthantFirstChartSimplex_face_flip n),
    orthantEquatorChain, map_sum]
  apply Finset.sum_congr rfl
  intro η _
  rw [map_zsmul, integralSimplexChain_map, orthantFirstChartSimplex_face_zero]

theorem orthantSecondHemisphereChain_boundary (n : ℕ) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (orthantSecondChart n)).d (n + 1) n (orthantSecondHemisphereChain n) =
      (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (orthantOverlapSecondInclusion n)).f n (orthantEquatorChain n) := by
  change (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) (TopCat.toSSet.obj (orthantSecondChart n))).d (n + 1) n
    (∑ η : Fin (n + 1) → Bool, OrthantSphereEquator.orthantWeight η •
      AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (orthantSecondChart n)) (OrthantHemisphereFaces.orthantSecondChartSimplex n η)) = _
  rw [OrthantWeightedBoundary.orthantWeighted_boundary_first _ n _ (OrthantHemisphereFaces.orthantSecondChartSimplex_face_flip n),
    orthantEquatorChain, map_sum]
  apply Finset.sum_congr rfl
  intro η _
  rw [map_zsmul, integralSimplexChain_map, orthantSecondChartSimplex_face_zero]

end

/-! The two hemisphere chains reconstruct the original full sphere chain. -/

open _root_.CategoryTheory
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def orthantHeadTailEquiv (n : ℕ) : (Fin (n + 1) → Bool) ≃ Bool × (Fin n → Bool) where
  toFun ε := (ε 0, Fin.tail ε)
  invFun p := Fin.cons p.1 p.2
  left_inv ε := by
    funext i
    refine Fin.cases rfl (fun _ => rfl) i
  right_inv p := rfl

theorem sum_orthant_head_tail {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : (Fin (n + 1) → Bool) → M) :
    (∑ ε, f ε) = (∑ η, f (Fin.cons false η)) + ∑ η, f (Fin.cons true η) := by
  have h : (∑ ε, f ε) = ∑ p : Bool × (Fin n → Bool), f (Fin.cons p.1 p.2) :=
    Fintype.sum_equiv (orthantHeadTailEquiv n) _ _ (fun ε => congrArg f ((orthantHeadTailEquiv n).symm_apply_apply ε).symm)
  rw [h, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]

theorem orientedOrthantSphereChain_split (n : ℕ) :
    OrthantSphereCycle.orientedOrthantSphereChain (n + 1) =
      -(∑ η : Fin (n + 1) → Bool, OrthantSphereEquator.orthantWeight η •
        AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1)))
          (OrthantSphereEquator.orthantSphereSimplex (n + 1) (Fin.cons false η))) +
      ∑ η : Fin (n + 1) → Bool, OrthantSphereEquator.orthantWeight η •
        AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1)))
          (OrthantSphereEquator.orthantSphereSimplex (n + 1) (Fin.cons true η)) := by
  rw [OrthantSphereCycle.orientedOrthantSphereChain, sum_orthant_head_tail]
  simp only [OrthantSphereEquator.orthantWeight_cons, OrthantSphereEquator.orthantSign, Bool.false_eq_true, ite_false, ite_true,
    neg_one_mul, one_mul, neg_zsmul, Finset.sum_neg_distrib]

theorem orthantFirstHemisphereChain_ambient (n : ℕ) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1)) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1))))).f (n + 1)
      (orthantFirstHemisphereChain n) =
    -(∑ η : Fin (n + 1) → Bool, OrthantSphereEquator.orthantWeight η •
      AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1)))
        (OrthantSphereEquator.orthantSphereSimplex (n + 1) (Fin.cons false η))) := by
  rw [orthantFirstHemisphereChain, map_neg, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro η _
  rw [map_zsmul, integralSimplexChain_map]
  rfl

theorem orthantSecondHemisphereChain_ambient (n : ℕ) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1)) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1))))).f (n + 1)
      (orthantSecondHemisphereChain n) =
    ∑ η : Fin (n + 1) → Bool, OrthantSphereEquator.orthantWeight η •
      AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1)))
        (OrthantSphereEquator.orthantSphereSimplex (n + 1) (Fin.cons true η)) := by
  rw [orthantSecondHemisphereChain, map_sum]
  apply Finset.sum_congr rfl
  intro η _
  rw [map_zsmul, integralSimplexChain_map]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantBoundaryRepresentatives
