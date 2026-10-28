import OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionSigns
import OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionOperator
import OAI.AlgebraicGeometry.CycleClass.Geometric.PermutationLast
import OAI.AlgebraicTopology.Cohomology.Singular.ChainDual
import Mathlib.GroupTheory.Perm.Fin

/-! # Subdivision Boundary -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionBoundary

noncomputable section

/-!
# Boundary compatibility of barycentric subdivision

The outer-face geometry identifies the remaining boundary terms after the
proved interior cancellation. All maps are the actual standard-simplex maps.
-/

open _root_.CategoryTheory
open scoped BigOperators Classical Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Cycles

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

variable {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]

private theorem zsmul_finset_sum {A J : Type*} [AddCommGroup A]
    (a : ℤ) (s : Finset J) (f : J → A) :
    a • ∑ j ∈ s, f j = ∑ j ∈ s, a • f j :=
  map_sum (zsmulAddGroupHom a) f s

omit [Fintype ι] in
/-- The ambient vertex interpolation map acts on a coordinate vector as expected. -/
@[simp]
theorem simplexVertexLinearMap_piSingle [DecidableEq κ]
    (v : κ → Convexity.StdSimplex ℝ ι) (k : κ) (a : ℝ) :
    BarycentricSimplex.Cycles.simplexVertexLinearMap v (Pi.single k a) = a • (v k : ι → ℝ) := by
  funext i
  simp [BarycentricSimplex.Cycles.simplexVertexLinearMap_apply, Pi.single_apply]

omit [Fintype ι] in
/-- Vertex interpolation is natural under a map of source vertices. -/
theorem simplexVertexLinearMap_precomp (v : κ → Convexity.StdSimplex ℝ ι) (f : η → κ) :
    (BarycentricSimplex.Cycles.simplexVertexLinearMap v).comp (FunOnFinite.linearMap ℝ ℝ f) =
      BarycentricSimplex.Cycles.simplexVertexLinearMap (fun k => v (f k)) := by
  classical
  apply LinearMap.pi_ext
  intro k a
  simp only [LinearMap.comp_apply, FunOnFinite.linearMap_piSingle,
    simplexVertexLinearMap_piSingle]

/-- Vertex interpolation is natural under a map of target vertices. -/
theorem simplexVertexLinearMap_postcomp (v : κ → Convexity.StdSimplex ℝ ι) (f : ι → η) :
    (FunOnFinite.linearMap ℝ ℝ f).comp (BarycentricSimplex.Cycles.simplexVertexLinearMap v) =
      BarycentricSimplex.Cycles.simplexVertexLinearMap (fun k => Convexity.StdSimplex.map f (v k)) := by
  classical
  apply LinearMap.pi_ext
  intro k a
  simp only [LinearMap.comp_apply, simplexVertexLinearMap_piSingle, map_smul,
    Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.map_coordinates]

/-- The source naturality identity holds for the genuine continuous simplex maps. -/
theorem simplexVertexMap_precomp_map (v : κ → Convexity.StdSimplex ℝ ι) (f : η → κ)
    (x : Convexity.StdSimplex ℝ η) :
    BarycentricSimplex.Cycles.simplexVertexMap v (Convexity.StdSimplex.map f x) =
      BarycentricSimplex.Cycles.simplexVertexMap (fun k => v (f k)) x := by
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).injective
  simp only [BarycentricSimplex.Cycles.simplexVertexMap_eq_affine, BarycentricSimplex.Cycles.simplexVertexAffineMap,
    LinearMap.coe_toAffineMap, Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.map_coordinates]
  exact congrArg (fun L : (η → ℝ) →ₗ[ℝ] (ι → ℝ) => L x)
    (simplexVertexLinearMap_precomp v f)

/-- The target naturality identity holds for the genuine continuous simplex maps. -/
theorem simplexVertexMap_postcomp_map (v : κ → Convexity.StdSimplex ℝ ι) (f : ι → η)
    (x : Convexity.StdSimplex ℝ κ) :
    Convexity.StdSimplex.map f (BarycentricSimplex.Cycles.simplexVertexMap v x) =
      BarycentricSimplex.Cycles.simplexVertexMap (fun k => Convexity.StdSimplex.map f (v k)) x := by
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).injective
  simp only [BarycentricSimplex.Cycles.simplexVertexMap_eq_affine, BarycentricSimplex.Cycles.simplexVertexAffineMap,
    LinearMap.coe_toAffineMap, Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.map_coordinates]
  exact congrArg (fun L : (κ → ℝ) →ₗ[ℝ] (η → ℝ) => L x)
    (simplexVertexLinearMap_postcomp v f)

/-- An injective vertex map carries the actual face barycenter to the mapped face barycenter. -/
theorem map_faceBarycenter (f : κ ↪ ι) (s : Finset κ) (hs : s.Nonempty) :
    Convexity.StdSimplex.map f (BarycentricSimplex.Cycles.faceBarycenter s hs) = BarycentricSimplex.Cycles.faceBarycenter (s.map f) hs.map := by
  classical
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).injective
  change ((Convexity.StdSimplex.map f (BarycentricSimplex.Cycles.faceBarycenter s hs)).weights : ι → ℝ) =
    ((BarycentricSimplex.Cycles.faceBarycenter (s.map f) hs.map).weights : ι → ℝ)
  rw [Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.map_coordinates]
  change FunOnFinite.linearMap ℝ ℝ f (BarycentricSimplex.Cycles.faceBarycenter s hs : κ → ℝ) =
    (BarycentricSimplex.Cycles.faceBarycenter (s.map f) hs.map : ι → ℝ)
  rw [BarycentricSimplex.Cycles.faceBarycenter_eq_centroid s hs, BarycentricSimplex.Cycles.faceBarycenter_eq_centroid (s.map f) hs.map,
    BarycentricMesh.centroid_eq_inv_card_sum s hs,
    BarycentricMesh.centroid_eq_inv_card_sum (s.map f) hs.map]
  simp only [map_smul, map_sum, Finset.card_map, Finset.sum_map,
    FunOnFinite.linearMap_piSingle]

/-- Initial faces of an inserted permutation are images of the smaller initial faces. -/
theorem outer_initial_face_eq {n : ℕ} (i : Fin (n + 2))
    (σ : Equiv.Perm (Fin (n + 2))) (τ : Equiv.Perm (Fin (n + 1)))
    (hσ : ∀ k, σ k.castSucc = i.succAbove (τ k)) (k : Fin (n + 1)) :
    (Finset.Iic k.castSucc).map σ.toEmbedding =
      ((Finset.Iic k).map τ.toEmbedding).map i.succAboveEmb := by
  rw [← Fin.map_castSuccEmb_Iic k, Finset.map_map, Finset.map_map]
  apply congrArg (fun e : Fin (n + 1) ↪ Fin (n + 2) => (Finset.Iic k).map e)
  apply Function.Embedding.ext
  intro j
  exact hσ j

/-- The last face of an inserted barycentric cell is exactly the corresponding
smaller cell followed by the original face inclusion. -/
theorem barycentricSubdivisionMap_comp_outer_face {n : ℕ}
    (i : Fin (n + 2)) (σ : Equiv.Perm (Fin (n + 2)))
    (τ : Equiv.Perm (Fin (n + 1)))
    (hσ : ∀ k, σ k.castSucc = i.succAbove (τ k)) :
    (BarycentricSimplex.Cycles.barycentricSubdivisionMap σ).comp
        (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace (Fin.last (n + 1))) =
      (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace i).comp
        (BarycentricSimplex.Cycles.barycentricSubdivisionMap τ) := by
  apply ContinuousMap.ext
  intro x
  change BarycentricSimplex.Cycles.simplexVertexMap
      (fun k => BarycentricSimplex.Cycles.faceBarycenter ((BarycentricSimplex.Cycles.permutationBarycentricFlag σ).face k)
        ((BarycentricSimplex.Cycles.permutationBarycentricFlag σ).nonempty k))
      (Convexity.StdSimplex.map (Fin.last (n + 1)).succAbove x) =
    Convexity.StdSimplex.map i.succAbove (BarycentricSimplex.Cycles.simplexVertexMap
      (fun k => BarycentricSimplex.Cycles.faceBarycenter ((BarycentricSimplex.Cycles.permutationBarycentricFlag τ).face k)
        ((BarycentricSimplex.Cycles.permutationBarycentricFlag τ).nonempty k)) x)
  rw [simplexVertexMap_precomp_map, simplexVertexMap_postcomp_map]
  apply congrArg (fun v => BarycentricSimplex.Cycles.simplexVertexMap v x)
  funext k
  simp only [Fin.succAbove_last_apply, BarycentricSimplex.Cycles.permutationBarycentricFlag]
  have h := map_faceBarycenter i.succAboveEmb
    ((Finset.Iic k).map τ.toEmbedding) ((BarycentricSimplex.Cycles.permutationBarycentricFlag τ).nonempty k)
  refine Eq.trans ?_ (by simpa only [Fin.coe_succAboveEmb] using h.symm)
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ _).injective
  funext a
  simp only [BarycentricSimplex.Cycles.faceBarycenter_apply]
  rw [outer_initial_face_eq i σ τ hσ k]

/-- The unit simplex generator, with the integral singular-chain model fixed explicitly. -/
def integralSimplexChain (X : TopCat.{0}) {n : ℕ} (s : SubdivisionOperator.Cycles.SingularSimplex X n) :
    (LocalHomology.Cycles.integralSingularChains X).X n :=
  (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s 1

/-- The subdivision formula on the unit simplex generators used in the chain complex. -/
theorem subdivisionDegree_simplexChain (X : TopCat.{0}) (n : ℕ)
    (s : SubdivisionOperator.Cycles.SingularSimplex X n) :
    SubdivisionOperator.Cycles.subdivisionDegree X n (integralSimplexChain X s) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
        integralSimplexChain X
          (SubdivisionOperator.Cycles.subdivisionSimplex X n s σ) := by
  rw [integralSimplexChain, SubdivisionOperator.Cycles.subdivisionDegree_simplex]
  apply Finset.sum_congr rfl
  intro σ _
  simpa only [integralSimplexChain, zsmul_eq_mul, mul_one] using!
    map_zsmul ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
      (SubdivisionOperator.Cycles.subdivisionSimplex X n s σ)).hom (Equiv.Perm.sign σ : ℤ) (1 : ℤ)

/-- The actual singular face of a subdivided simplex has the expected composite map. -/
theorem subdivisionSimplex_face_continuous (X : TopCat.{0}) (n : ℕ)
    (s : SubdivisionOperator.Cycles.SingularSimplex X (n + 1)) (σ : Equiv.Perm (Fin (n + 2)))
    (i : Fin (n + 2)) :
    AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n
      ((TopCat.toSSet.obj X).δ i (SubdivisionOperator.Cycles.subdivisionSimplex X (n + 1) s σ)) =
      (AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X (n + 1) s).comp
        ((BarycentricSimplex.Cycles.barycentricSubdivisionMap σ).comp (AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.standardSimplexFace i)) := by
  rw [AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.singularSimplicesEquivContinuousMap_face]
  change (X.toSSetObjEquiv (.op ⦋n + 1⦌) (SubdivisionOperator.Cycles.subdivisionSimplex X (n + 1) s σ)).comp _ = _
  rw [SubdivisionOperator.Cycles.subdivisionSimplex_toContinuousMap]
  rfl

/-- The paired interior faces are equal as actual singular simplices. -/
theorem subdivisionSimplex_inner_face_swap (X : TopCat.{0}) (n : ℕ)
    (s : SubdivisionOperator.Cycles.SingularSimplex X (n + 1)) (σ : Equiv.Perm (Fin (n + 2)))
    (j : Fin (n + 1)) :
    (TopCat.toSSet.obj X).δ j.castSucc
      (SubdivisionOperator.Cycles.subdivisionSimplex X (n + 1) s (σ * Equiv.swap j.castSucc j.succ)) =
      (TopCat.toSSet.obj X).δ j.castSucc (SubdivisionOperator.Cycles.subdivisionSimplex X (n + 1) s σ) := by
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n).injective
  rw [subdivisionSimplex_face_continuous, subdivisionSimplex_face_continuous,
    SubdivisionSigns.Cycles.barycentricSubdivisionMap_comp_inner_face_swap]

/-- Outer-face compatibility holds at the actual singular-simplex level. -/
theorem subdivisionSimplex_outer_face (X : TopCat.{0}) (n : ℕ)
    (s : SubdivisionOperator.Cycles.SingularSimplex X (n + 1)) (i : Fin (n + 2))
    (σ : Equiv.Perm (Fin (n + 2))) (τ : Equiv.Perm (Fin (n + 1)))
    (hσ : ∀ k, σ k.castSucc = i.succAbove (τ k)) :
    (TopCat.toSSet.obj X).δ (Fin.last (n + 1)) (SubdivisionOperator.Cycles.subdivisionSimplex X (n + 1) s σ) =
      SubdivisionOperator.Cycles.subdivisionSimplex X n ((TopCat.toSSet.obj X).δ i s) τ := by
  apply (AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n).injective
  rw [subdivisionSimplex_face_continuous]
  change _ = X.toSSetObjEquiv (.op ⦋n⦌) (SubdivisionOperator.Cycles.subdivisionSimplex X n _ τ)
  rw [SubdivisionOperator.Cycles.subdivisionSimplex_toContinuousMap]
  change _ = (AlgebraicTopology.Cohomology.Singular.Coefficients.singularSimplicesEquivContinuousMap X n
    ((TopCat.toSSet.obj X).δ i s)).comp _
  rw [AlgebraicTopology.Cohomology.Singular.ContinuousFormulas.singularSimplicesEquivContinuousMap_face,
    barycentricSubdivisionMap_comp_outer_face i σ τ hσ]
  rfl

/-- Each interior contribution vanishes in the unit-generator chain notation. -/
theorem subdivision_inner_chain_sum_zero (X : TopCat.{0}) (n : ℕ)
    (s : SubdivisionOperator.Cycles.SingularSimplex X (n + 1)) (j : Fin (n + 1)) :
    (∑ σ : Equiv.Perm (Fin (n + 2)),
      ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ j.val) •
        integralSimplexChain X
          ((TopCat.toSSet.obj X).δ j.castSucc (SubdivisionOperator.Cycles.subdivisionSimplex X (n + 1) s σ))) = 0 := by
  simp only [mul_smul]
  apply SubdivisionSigns.Cycles.sum_perm_sign_eq_zero_of_swap_invariant j.castSucc j.succ
    (ne_of_lt j.castSucc_lt_succ)
  intro σ
  rw [subdivisionSimplex_inner_face_swap]

/-- The outer faces reindex exactly by an original face and its subdivision cell,
with the correct integral orientation coefficient. -/
theorem subdivision_outer_chain_sum (X : TopCat.{0}) (n : ℕ)
    (s : SubdivisionOperator.Cycles.SingularSimplex X (n + 1)) :
    (∑ σ : Equiv.Perm (Fin (n + 2)),
      ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ (n + 1)) •
        integralSimplexChain X
          ((TopCat.toSSet.obj X).δ (Fin.last (n + 1))
            (SubdivisionOperator.Cycles.subdivisionSimplex X (n + 1) s σ))) =
      ∑ i : Fin (n + 2), ∑ τ : Equiv.Perm (Fin (n + 1)),
        ((-1 : ℤ) ^ i.val * (Equiv.Perm.sign τ : ℤ)) •
          integralSimplexChain X
            (SubdivisionOperator.Cycles.subdivisionSimplex X n ((TopCat.toSSet.obj X).δ i s) τ) := by
  rw [← (PermutationLast.Cycles.insertLastPermutationEquiv n).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro τ _
  simp only [PermutationLast.Cycles.insertLastPermutationEquiv_apply, PermutationLast.Cycles.sign_insertLastPermutation]
  rw [subdivisionSimplex_outer_face X n s i (PermutationLast.Cycles.insertLastPermutation i τ) τ
    (PermutationLast.Cycles.insertLastPermutation_apply_castSucc i τ)]

/-- The unit-generator boundary formula in the integral singular-chain model. -/
theorem integralSimplexChain_boundary (X : TopCat.{0}) (n : ℕ)
    (s : SubdivisionOperator.Cycles.SingularSimplex X (n + 1)) :
    (LocalHomology.Cycles.integralSingularChains X).d (n + 1) n
      (integralSimplexChain X s) =
        ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
          integralSimplexChain X
            ((TopCat.toSSet.obj X).δ i s) := by
  simpa only [integralSimplexChain, AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain] using!
    (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain_boundary (R := ℤ) (TopCat.toSSet.obj X) s)

/-- Expanding the actual boundary of a subdivided simplex gives the finite sum
over all its geometric faces and all permutation cells. -/
theorem boundary_subdivision_simplexChain_expansion (X : TopCat.{0}) (n : ℕ)
    (s : SubdivisionOperator.Cycles.SingularSimplex X (n + 1)) :
    (LocalHomology.Cycles.integralSingularChains X).d (n + 1) n
        (SubdivisionOperator.Cycles.subdivisionDegree X (n + 1)
          (integralSimplexChain X s)) =
      ∑ i : Fin (n + 2), ∑ σ : Equiv.Perm (Fin (n + 2)),
        ((Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ i.val) •
          integralSimplexChain X
            ((TopCat.toSSet.obj X).δ i (SubdivisionOperator.Cycles.subdivisionSimplex X (n + 1) s σ)) := by
  rw [subdivisionDegree_simplexChain, map_sum]
  simp only [map_zsmul, integralSimplexChain_boundary,
    zsmul_finset_sum, ← mul_zsmul]
  exact Finset.sum_comm

/-- Barycentric subdivision commutes with the actual singular boundary on each
unit simplex generator. Interior faces cancel and the outer faces are precisely
the subdivisions of the original boundary. -/
theorem boundary_subdivision_simplexChain (X : TopCat.{0}) (n : ℕ)
    (s : SubdivisionOperator.Cycles.SingularSimplex X (n + 1)) :
    (LocalHomology.Cycles.integralSingularChains X).d (n + 1) n
        (SubdivisionOperator.Cycles.subdivisionDegree X (n + 1)
          (integralSimplexChain X s)) =
      SubdivisionOperator.Cycles.subdivisionDegree X n ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n
        (integralSimplexChain X s)) := by
  rw [boundary_subdivision_simplexChain_expansion, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, subdivision_inner_chain_sum_zero,
    Finset.sum_const_zero, zero_add, Fin.val_last]
  rw [subdivision_outer_chain_sum, integralSimplexChain_boundary, map_sum]
  simp only [map_zsmul, subdivisionDegree_simplexChain, zsmul_finset_sum, ← mul_zsmul]

/-- The actual degreewise linear maps commute with the actual singular differential. -/
theorem subdivisionDegree_comm (X : TopCat.{0}) (n : ℕ) :
    ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n).hom.comp (SubdivisionOperator.Cycles.subdivisionDegree X (n + 1)) =
      (SubdivisionOperator.Cycles.subdivisionDegree X n).comp ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n).hom := by
  apply AlgebraicTopology.Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj X)
    ((LocalHomology.Cycles.integralSingularChains X).X n)
  intro s
  simpa only [integralSimplexChain, AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain,
    LinearMap.comp_apply] using! boundary_subdivision_simplexChain X n s

/-- Pointwise boundary compatibility for arbitrary actual integral singular chains. -/
theorem subdivisionDegree_boundary (X : TopCat.{0}) (n : ℕ)
    (c : (LocalHomology.Cycles.integralSingularChains X).X (n + 1)) :
    (LocalHomology.Cycles.integralSingularChains X).d (n + 1) n (SubdivisionOperator.Cycles.subdivisionDegree X (n + 1) c) =
      SubdivisionOperator.Cycles.subdivisionDegree X n ((LocalHomology.Cycles.integralSingularChains X).d (n + 1) n c) :=
  LinearMap.congr_fun (subdivisionDegree_comm X n) c

/-- The genuine integral barycentric subdivision chain map. Its components are
the explicitly constructed signed sums of geometric subdivision cells. -/
def subdivisionChainMap (X : TopCat.{0}) :
    LocalHomology.Cycles.integralSingularChains X ⟶ LocalHomology.Cycles.integralSingularChains X :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (SubdivisionOperator.Cycles.subdivisionDegree X n)) (fun n => by
    apply ModuleCat.hom_ext
    exact subdivisionDegree_comm X n)

/-- The chain-map packaging preserves the previously defined degreewise operator. -/
@[simp]
theorem subdivisionChainMap_f (X : TopCat.{0}) (n : ℕ) :
    ((subdivisionChainMap X).f n).hom = SubdivisionOperator.Cycles.subdivisionDegree X n := rfl

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionBoundary
