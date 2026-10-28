import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantSphereEquator
import OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives

/-! # Orthant Sphere Cycle -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantSphereCycle

noncomputable section

/-!
# ChernClass: the actual integral oriented sphere chain

The signed sum of all coordinate orthants is a cycle. Every omitted face
is paired with the identical face in the neighboring orthant with opposite
coefficient. The proof computes the original singular-chain differential.
-/

open OAI.AlgebraicTopology.Cohomology.Singular.ChainRepresentatives
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def orientedOrthantSphereChain (n : ℕ) : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n)).X n :=
  ∑ ε : Fin (n + 1) → Bool, OrthantSphereEquator.orthantWeight ε •
    AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n)) (OrthantSphereEquator.orthantSphereSimplex n ε)

theorem orientedOrthantFace_sum_zero (n : ℕ) (i : Fin (n + 2)) :
    (∑ ε : Fin (n + 2) → Bool, OrthantSphereEquator.orthantWeight ε • (((-1 : ℤ) ^ i.val) •
      AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1)))
        ((TopCat.toSSet.obj (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1))).δ i (OrthantSphereEquator.orthantSphereSimplex (n + 1) ε)))) = 0 := by
  classical
  apply Finset.sum_ninvolution (OrthantSphereEquator.orthantFlip i)
  · intro ε
    have hf : (TopCat.toSSet.obj (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1))).δ i
        (OrthantSphereEquator.orthantSphereSimplex (n + 1) (OrthantSphereEquator.orthantFlip i ε)) =
      (TopCat.toSSet.obj (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1))).δ i (OrthantSphereEquator.orthantSphereSimplex (n + 1) ε) :=
      OrthantSphereEquator.orthantSphereSimplex_face_update ε i (!(ε i))
    rw [OrthantSphereEquator.orthantWeight_flip, hf, neg_zsmul, add_neg_cancel]
  · intro ε _
    exact OrthantSphereEquator.orthantFlip_ne i ε
  · intro ε
    exact Finset.mem_univ _
  · exact OrthantSphereEquator.orthantFlip_involutive i

theorem orientedOrthantSphereChain_boundary (n : ℕ) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1))).d (n + 1) n
      (orientedOrthantSphereChain (n + 1)) = 0 := by
  change (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) (TopCat.toSSet.obj (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1)))).d (n + 1) n
    (∑ ε : Fin (n + 2) → Bool, OrthantSphereEquator.orthantWeight ε •
      AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1))) (OrthantSphereEquator.orthantSphereSimplex (n + 1) ε)) = 0
  rw [map_sum]
  simp only [map_zsmul, AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain_boundary]
  have hs (ε : Fin (n + 2) → Bool) :
      OrthantSphereEquator.orthantWeight ε • (∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
        AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1)))
          ((TopCat.toSSet.obj (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1))).δ i (OrthantSphereEquator.orthantSphereSimplex (n + 1) ε))) =
      ∑ i : Fin (n + 2), OrthantSphereEquator.orthantWeight ε • (((-1 : ℤ) ^ i.val) •
        AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1)))
          ((TopCat.toSSet.obj (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1))).δ i (OrthantSphereEquator.orthantSphereSimplex (n + 1) ε))) :=
    map_sum (zsmulAddGroupHom (OrthantSphereEquator.orthantWeight ε)) _ _
  simp_rw [hs]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun i _ => orientedOrthantFace_sum_zero n i

def orientedOrthantSphereCycle (n : ℕ) : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n)) n :=
  ⟨orientedOrthantSphereChain n, by
    cases n with
    | zero => exact AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero _ _
    | succ n =>
      rw [AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ]
      exact orientedOrthantSphereChain_boundary n⟩

def orientedOrthantSphereClass (n : ℕ) : CycleClass.Geometric.RelativeHomologyExact.Cycles.integralSingularHomology (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n) n :=
  AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n)) n (orientedOrthantSphereCycle n)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantSphereCycle
