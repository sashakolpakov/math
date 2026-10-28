import OAI.AlgebraicTopology.Products.SimplexReversal
import OAI.AlgebraicTopology.Products.ReversalSigns
import OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

/-! # Singular Reversal -/

namespace OAI.AlgebraicTopology.Products.SingularReversal

noncomputable section

/-!
# Signed reversal of actual singular chains

Reversing simplex coordinates is an actual continuous self-map of the
topological simplex, rather than a morphism of the simplex category.
Multiplication in degree `n` by `(-1)^(n*(n+1)/2)` makes precomposition by
this reversal commute with the ordinary singular boundary.
-/

open _root_.CategoryTheory
open scoped Simplicial
open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy.Cycles

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem zsmul_finset_sum {A J : Type*} [AddCommGroup A]
    (a : ℤ) (s : Finset J) (f : J → A) :
    a • ∑ j ∈ s, f j = ∑ j ∈ s, a • f j :=
  map_sum (zsmulAddGroupHom a) f s

private theorem integral_simplexChain_boundary (X : TopCat.{0}) (n : ℕ)
    (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d (n + 1) n
        (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) s) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
        Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) ((TopCat.toSSet.obj X).δ i s) := by
  simpa only [AlgebraicGeometry.CycleClass.Geometric.SubdivisionBoundary.Cycles.integralSimplexChain, Cohomology.Singular.ChainDual.simplexChain] using! AlgebraicGeometry.CycleClass.Geometric.SubdivisionBoundary.Cycles.integralSimplexChain_boundary X n s

/-- The actual integral-linear extension of signed coordinate reversal on
continuous singular simplices. -/
def singularReversalDegree (X : TopCat.{0}) (n : ℕ) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n :=
  Cohomology.Singular.ChainDual.chainFunctionalOfFunction (TopCat.toSSet.obj X) ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) n
    (fun s => ReversalSigns.reversalSign n •
      Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) (SimplexReversal.singularSimplexReversal X n s))

/-- The defining value of reversal on each actual unit simplex generator. -/
@[simp]
theorem singularReversalDegree_simplex (X : TopCat.{0}) (n : ℕ)
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    singularReversalDegree X n (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) s) =
      ReversalSigns.reversalSign n •
        Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) (SimplexReversal.singularSimplexReversal X n s) :=
  Cohomology.Singular.ChainDual.chainFunctionalOfFunction_simplex _ _ _ _ _

/-- The signed reversal fixes degree-zero integral chains. -/
@[simp]
theorem singularReversalDegree_zero (X : TopCat.{0}) :
    singularReversalDegree X 0 = LinearMap.id := by
  apply Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj X) ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X 0)
  intro s
  simpa only [ReversalSigns.reversalSign_zero, SimplexReversal.singularSimplexReversal_zero, one_smul,
    LinearMap.id_apply] using! singularReversalDegree_simplex X 0 s

/-- Reversal commutes with continuous postcomposition on actual chains. -/
theorem singularReversalDegree_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    (AlgebraicGeometry.CycleClass.Geometric.SubdivisionNaturality.Cycles.singularChainPostcompose f n).comp (singularReversalDegree X n) =
      (singularReversalDegree Y n).comp (AlgebraicGeometry.CycleClass.Geometric.SubdivisionNaturality.Cycles.singularChainPostcompose f n) := by
  apply Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj X) ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains Y).X n)
  intro s
  have hpush (t : (TopCat.toSSet.obj X) _⦋n⦌) :
      AlgebraicGeometry.CycleClass.Geometric.SubdivisionNaturality.Cycles.singularChainPostcompose f n (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) t) =
        Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj Y) ((TopCat.toSSet.map f).app _ t) :=
    AlgebraicGeometry.CycleClass.Geometric.SubdivisionNaturality.Cycles.singularChainPostcompose_simplex f n t 1
  have hnat : AlgebraicGeometry.CycleClass.Geometric.SubdivisionNaturality.Cycles.singularChainPostcompose f n
        (singularReversalDegree X n (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) s)) =
      singularReversalDegree Y n
        (AlgebraicGeometry.CycleClass.Geometric.SubdivisionNaturality.Cycles.singularChainPostcompose f n (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) s)) := by
    rw [singularReversalDegree_simplex, map_zsmul, hpush, hpush,
      singularReversalDegree_simplex, SimplexReversal.singularSimplexReversal_naturality]
  simpa only [LinearMap.comp_apply] using! hnat

theorem singularReversalDegree_naturality_apply
    {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    AlgebraicGeometry.CycleClass.Geometric.SubdivisionNaturality.Cycles.singularChainPostcompose f n (singularReversalDegree X n z) =
      singularReversalDegree Y n (AlgebraicGeometry.CycleClass.Geometric.SubdivisionNaturality.Cycles.singularChainPostcompose f n z) :=
  LinearMap.congr_fun (singularReversalDegree_naturality f n) z

/-- On an actual simplex the reversed face order and the triangular sign
give the ordinary singular boundary exactly. -/
theorem singularReversalDegree_boundary_simplex
    (X : TopCat.{0}) (n : ℕ) (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d (n + 1) n
        (singularReversalDegree X (n + 1)
          (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) s)) =
      singularReversalDegree X n
        ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d (n + 1) n
          (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) s)) := by
  simp only [singularReversalDegree_simplex, map_zsmul, integral_simplexChain_boundary,
    zsmul_finset_sum, map_sum, SimplexReversal.singularSimplexReversal_face, smul_smul]
  apply Fintype.sum_equiv (Fin.revPerm) _ _
  intro i
  simp only [Fin.revPerm_apply]
  rw [ReversalSigns.reversalSign_face]
  congr 1
  exact mul_comm _ _

/-- Integral-linear boundary compatibility, established on the actual free
simplex generators. -/
theorem singularReversalDegree_boundary_comm (X : TopCat.{0}) (n : ℕ) :
    ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d (n + 1) n).hom.comp (singularReversalDegree X (n + 1)) =
      (singularReversalDegree X n).comp ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d (n + 1) n).hom := by
  apply Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj X) ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n)
  intro s
  exact singularReversalDegree_boundary_simplex X n s

/-- Pointwise boundary compatibility on arbitrary finite singular chains. -/
theorem singularReversalDegree_boundary (X : TopCat.{0}) (n : ℕ)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X (n + 1)) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d (n + 1) n (singularReversalDegree X (n + 1) z) =
      singularReversalDegree X n ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d (n + 1) n z) :=
  LinearMap.congr_fun (singularReversalDegree_boundary_comm X n) z

/-- Reversal commutes with every differential, including off-shape maps. -/
theorem singularReversalDegree_comm (X : TopCat.{0}) (i j : ℕ) :
    ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d i j).hom.comp (singularReversalDegree X i) =
      (singularReversalDegree X j).comp ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d i j).hom := by
  by_cases h : (ComplexShape.down ℕ).Rel i j
  · have hi : j + 1 = i := h
    subst i
    exact singularReversalDegree_boundary_comm X j
  · rw [(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).shape i j h]
    simp

/-- The signed reversal as an endomorphism of the actual singular chain
complex in the functor category of topological spaces. -/
def naturalSingularReversal : AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy.Cycles.naturalSingularChains ⟶ AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy.Cycles.naturalSingularChains where
  f n :=
    { app X := ModuleCat.ofHom (singularReversalDegree X n)
      naturality X Y f := by
        apply ModuleCat.hom_ext
        exact (singularReversalDegree_naturality f n).symm }
  comm' i j _ := by
    apply NatTrans.ext
    funext X
    apply ModuleCat.hom_ext
    exact singularReversalDegree_comm X i j

/-- The natural reversal agrees with the identity in degree zero. -/
theorem naturalSingularReversal_zero :
    naturalSingularReversal.f 0 = 𝟙 (AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy.Cycles.singularChainDegreeFunctor 0) := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  exact singularReversalDegree_zero X

/-- Signed reversal evaluated on an actual topological space. -/
def singularReversalChainMap (X : TopCat.{0}) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X ⟶ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X :=
  AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy.Cycles.naturalSingularChainMapAt naturalSingularReversal X

@[simp]
theorem singularReversalChainMap_f_apply (X : TopCat.{0}) (n : ℕ)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    (singularReversalChainMap X).f n z = singularReversalDegree X n z := rfl

@[simp]
theorem singularReversalChainMap_simplex (X : TopCat.{0}) (n : ℕ)
    (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    (singularReversalChainMap X).f n (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) s) =
      ReversalSigns.reversalSign n •
        Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) (SimplexReversal.singularSimplexReversal X n s) :=
  singularReversalDegree_simplex X n s

@[simp]
theorem singularReversalChainMap_zero (X : TopCat.{0}) :
    (singularReversalChainMap X).f 0 = 𝟙 ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X 0) := by
  apply ModuleCat.hom_ext
  exact singularReversalDegree_zero X

/-- The evaluated chain maps commute with every actual continuous map. -/
@[reassoc]
theorem singularReversalChainMap_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f ≫ singularReversalChainMap Y =
      singularReversalChainMap X ≫ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f := by
  apply HomologicalComplex.hom_ext
  intro n
  exact (naturalSingularReversal.f n).naturality f

end

end OAI.AlgebraicTopology.Products.SingularReversal
