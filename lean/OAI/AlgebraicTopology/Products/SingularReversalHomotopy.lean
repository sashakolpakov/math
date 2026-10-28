import OAI.AlgebraicTopology.Products.SingularReversal
import OAI.AlgebraicTopology.Products.SingularChainScalarExtension
import OAI.AlgebraicTopology.Products.SingularChainDualTransport

/-! # Singular Reversal Homotopy -/

namespace OAI.AlgebraicTopology.Products.SingularReversalHomotopy

noncomputable section

/-!
# Signed singular reversal is naturally homotopic to the identity

The integral homotopy is obtained from the proved natural simplex-filling
construction. Tensor extension and linear duality transport it to genuine
scalar chains and coefficient-valued cochains. Its component naturality
includes every subspace inclusion, as required for relative descent.
-/

open _root_.CategoryTheory
open scoped Simplicial TensorProduct ChangeOfRings

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Signed reversal and the identity have the same degree-zero component,
so the actual natural filling construction produces this homotopy. -/
def naturalSingularReversalHomotopy :
    Homotopy SingularReversal.naturalSingularReversal (𝟙 AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy.Cycles.naturalSingularChains) :=
  AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy.Cycles.naturalSingularHomotopy SingularReversal.naturalSingularReversal (𝟙 AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy.Cycles.naturalSingularChains)
    SingularReversal.naturalSingularReversal_zero

def singularReversalHomotopy (X : TopCat.{0}) :
    Homotopy (SingularReversal.singularReversalChainMap X) (𝟙 (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X)) :=
  AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy.Cycles.naturalSingularHomotopyAt naturalSingularReversalHomotopy X

@[reassoc]
theorem singularReversalHomotopy_naturality {X Y : TopCat.{0}}
    (f : X ⟶ Y) (i j : ℕ) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f).f i ≫ (singularReversalHomotopy Y).hom i j =
      (singularReversalHomotopy X).hom i j ≫ (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f).f j :=
  (naturalSingularReversalHomotopy.hom i j).naturality f

@[reassoc]
theorem singularReversalHomotopy_subspace (X : TopCat.{0}) (A : Set X) (i j : ℕ) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A).f i ≫ (singularReversalHomotopy X).hom i j =
      (singularReversalHomotopy (TopCat.of A)).hom i j ≫ (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A).f j :=
  singularReversalHomotopy_naturality (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A) i j

theorem singularReversalChainMap_homologyMap (X : TopCat.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap (SingularReversal.singularReversalChainMap X) n = 𝟙 _ := by
  simpa only [HomologicalComplex.homologyMap_id] using
    (singularReversalHomotopy X).homologyMap_eq n

variable {R : Type} [CommRing R]

/-- The actual integral reversal transported to scalar singular chains. -/
def singularScalarReversalChainMap (X : TopCat.{0}) :
    Cohomology.Singular.Evaluation.singularScalarChains (R := R) X ⟶ Cohomology.Singular.Evaluation.singularScalarChains (R := R) X :=
  SingularChainScalarExtension.scalarExtendSingularMap R (SingularReversal.singularReversalChainMap X)

@[reassoc]
theorem singularScalarReversalChainMap_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f ≫ singularScalarReversalChainMap Y =
      singularScalarReversalChainMap X ≫ Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f := by
  rw [← SingularChainScalarExtension.scalarExtendSingularMap_continuous R f]
  change SingularChainScalarExtension.scalarExtendSingularMap R (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f) ≫
      SingularChainScalarExtension.scalarExtendSingularMap R (SingularReversal.singularReversalChainMap Y) =
    SingularChainScalarExtension.scalarExtendSingularMap R (SingularReversal.singularReversalChainMap X) ≫
      SingularChainScalarExtension.scalarExtendSingularMap R (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f)
  rw [← SingularChainScalarExtension.scalarExtendSingularMap_comp, ← SingularChainScalarExtension.scalarExtendSingularMap_comp,
    SingularReversal.singularReversalChainMap_naturality]

@[simp]
theorem singularScalarReversalChainMap_simplex (X : TopCat.{0}) (n : ℕ)
    (s : Cohomology.Singular.Basic.singularSimplices X n) :
    (singularScalarReversalChainMap (R := R) X).f n
        (Cohomology.Singular.ChainDual.simplexChain (R := R) (TopCat.toSSet.obj X) s) =
      ReversalSigns.reversalSign n • Cohomology.Singular.ChainDual.simplexChain (R := R) (TopCat.toSSet.obj X)
        (SimplexReversal.singularSimplexReversal X n s) := by
  change (SingularChainScalarExtension.integralScalarSingularChainsIso R X).hom.f n
    ((SingularChainScalarExtension.integralScalarExtension R).map ((SingularReversal.singularReversalChainMap X).f n)
      ((SingularChainScalarExtension.integralScalarSingularChainsIso R X).inv.f n
        (Cohomology.Singular.ChainDual.simplexChain (R := R) (TopCat.toSSet.obj X) s))) = _
  rw [SingularChainScalarExtension.integralScalarSingularChainsIso_inv_simplex]
  change (SingularChainScalarExtension.integralScalarSingularChainsIso R X).hom.f n
    ((1 : R) ⊗ₜ[ℤ, Int.castRingHom R]
      ((SingularReversal.singularReversalChainMap X).f n
        (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) s))) = _
  rw [SingularReversal.singularReversalChainMap_simplex]
  have ht := map_zsmul
    (TensorProduct.mk ℤ
      ((ModuleCat.restrictScalars (Int.castRingHom R)).obj (ModuleCat.of R R))
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) (1 : R))
    (ReversalSigns.reversalSign n)
    (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) (SimplexReversal.singularSimplexReversal X n s))
  have ht' :
      (1 : R) ⊗ₜ[ℤ, Int.castRingHom R]
          (ReversalSigns.reversalSign n • Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X)
            (SimplexReversal.singularSimplexReversal X n s)) =
        ReversalSigns.reversalSign n • ((1 : R) ⊗ₜ[ℤ, Int.castRingHom R]
          Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) (SimplexReversal.singularSimplexReversal X n s)) := by
    simpa only [TensorProduct.mk_apply] using! ht
  rw [ht', map_zsmul, SingularChainScalarExtension.integralScalarSingularChainsIso_hom_one_tmul_simplex]

/-- Tensor transport of the genuine integral reversal homotopy. -/
def singularScalarReversalHomotopy (X : TopCat.{0}) :
    Homotopy (singularScalarReversalChainMap (R := R) X)
      (𝟙 (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X)) where
  hom := (SingularChainScalarExtension.scalarExtendSingularHomotopy R (singularReversalHomotopy X)).hom
  zero := (SingularChainScalarExtension.scalarExtendSingularHomotopy R (singularReversalHomotopy X)).zero
  comm i := by
    simpa only [SingularChainScalarExtension.scalarExtendSingularMap_id, singularScalarReversalChainMap] using!
      (SingularChainScalarExtension.scalarExtendSingularHomotopy R (singularReversalHomotopy X)).comm i

@[reassoc]
theorem singularScalarReversalHomotopy_naturality {X Y : TopCat.{0}}
    (f : X ⟶ Y) (i j : ℕ) :
    (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f).f i ≫
        (singularScalarReversalHomotopy (R := R) Y).hom i j =
      (singularScalarReversalHomotopy (R := R) X).hom i j ≫
        (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f).f j :=
  SingularChainScalarExtension.scalarExtendSingularHomotopy_naturality R f
    (singularReversalHomotopy X) (singularReversalHomotopy Y)
    (singularReversalHomotopy_naturality f) i j

theorem singularScalarReversalChainMap_homologyMap (X : TopCat.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap (singularScalarReversalChainMap (R := R) X) n = 𝟙 _ := by
  simpa only [HomologicalComplex.homologyMap_id] using
    (singularScalarReversalHomotopy (R := R) X).homologyMap_eq n

/-- Signed reversal on genuine coefficient-valued singular cochains. -/
def singularReversalCochainMap (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    Cohomology.Singular.Basic.singularCochains M X ⟶ Cohomology.Singular.Basic.singularCochains M X :=
  SingularChainDualTransport.singularDualCochainMap M (singularScalarReversalChainMap (R := R) X)

/-- The transported operator has exactly the signed reversed-simplex
evaluation formula. -/
theorem evaluation_singularReversalCochainMap (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (n : ℕ) (c : (Cohomology.Singular.Basic.singularCochains M X).X n)
    (s : Cohomology.Singular.Basic.singularSimplices X n) :
    Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) M s
        ((singularReversalCochainMap M X).f n c) =
      ReversalSigns.reversalSign n • Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj X) M
        (SimplexReversal.singularSimplexReversal X n s) c := by
  have h := LinearMap.congr_fun
    (SingularChainDualTransport.singularDualCochainMap_dual M (singularScalarReversalChainMap (R := R) X) n c)
    (Cohomology.Singular.ChainDual.simplexChain (R := R) (TopCat.toSSet.obj X) s)
  simpa only [Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv, Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex,
    LinearMap.comp_apply, singularScalarReversalChainMap_simplex, map_zsmul,
    singularReversalCochainMap] using! h

@[reassoc]
theorem singularReversalCochainMap_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) :
    singularReversalCochainMap M Y ≫ Cohomology.Singular.Functor.singularPullback M f =
      Cohomology.Singular.Functor.singularPullback M f ≫ singularReversalCochainMap M X := by
  rw [← SingularChainDualTransport.singularDualCochainMap_continuous M f]
  change SingularChainDualTransport.singularDualCochainMap M (singularScalarReversalChainMap Y) ≫
      SingularChainDualTransport.singularDualCochainMap M (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap f) =
    SingularChainDualTransport.singularDualCochainMap M (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap f) ≫
      SingularChainDualTransport.singularDualCochainMap M (singularScalarReversalChainMap X)
  rw [← SingularChainDualTransport.singularDualCochainMap_comp, ← SingularChainDualTransport.singularDualCochainMap_comp,
    singularScalarReversalChainMap_naturality]

/-- Dualizing the actual scalar chain homotopy gives a homotopy on the
existing coefficient-valued cochain complex. -/
def singularReversalCochainHomotopy (M : ModuleCat.{0} R) (X : TopCat.{0}) :
    Homotopy (singularReversalCochainMap M X) (𝟙 (Cohomology.Singular.Basic.singularCochains M X)) where
  hom := (SingularChainDualTransport.singularDualCochainHomotopy M (singularScalarReversalHomotopy X)).hom
  zero := (SingularChainDualTransport.singularDualCochainHomotopy M (singularScalarReversalHomotopy X)).zero
  comm i := by
    simpa only [SingularChainDualTransport.singularDualCochainMap_id, singularReversalCochainMap] using!
      (SingularChainDualTransport.singularDualCochainHomotopy M (singularScalarReversalHomotopy X)).comm i

@[reassoc]
theorem singularReversalCochainHomotopy_naturality (M : ModuleCat.{0} R)
    {X Y : TopCat.{0}} (f : X ⟶ Y) (i j : ℕ) :
    (singularReversalCochainHomotopy M Y).hom i j ≫ (Cohomology.Singular.Functor.singularPullback M f).f j =
      (Cohomology.Singular.Functor.singularPullback M f).f i ≫ (singularReversalCochainHomotopy M X).hom i j :=
  SingularChainDualTransport.singularDualCochainHomotopy_naturality M f
    (singularScalarReversalHomotopy X) (singularScalarReversalHomotopy Y)
    (singularScalarReversalHomotopy_naturality f) i j

@[reassoc]
theorem singularReversalCochainHomotopy_subspace (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (A : Set X) (i j : ℕ) :
    (singularReversalCochainHomotopy M X).hom i j ≫
        (Cohomology.Singular.Functor.singularPullback M (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A)).f j =
      (Cohomology.Singular.Functor.singularPullback M (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A)).f i ≫
        (singularReversalCochainHomotopy M (TopCat.of A)).hom i j :=
  singularReversalCochainHomotopy_naturality M (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A) i j

/-- Signed reversal induces the identity on genuine singular cohomology. -/
theorem singularReversalCochainMap_homologyMap (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap (singularReversalCochainMap M X) n = 𝟙 _ := by
  simpa only [HomologicalComplex.homologyMap_id] using
    (singularReversalCochainHomotopy M X).homologyMap_eq n

end

end OAI.AlgebraicTopology.Products.SingularReversalHomotopy
