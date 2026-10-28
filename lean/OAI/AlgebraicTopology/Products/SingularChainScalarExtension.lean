import OAI.AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
import OAI.AlgebraicTopology.Products.IntegralScalarUnit

/-! # Singular Chain Scalar Extension -/

namespace OAI.AlgebraicTopology.Products.SingularChainScalarExtension

noncomputable section

/-!
# Scalar extension of genuine integral singular chains

The tensor extension functor commutes with the coproduct construction of
singular chains. The comparison below is the previously proved coefficient
functor comparison, with the tensor unit identified explicitly.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial TensorProduct ChangeOfRings

open OAI.AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type) [CommRing R]

/-- Tensor extension along the canonical integer coefficient map. -/
abbrev integralScalarExtension : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} R :=
  ModuleCat.extendScalars (Int.castRingHom R)

instance integralScalarExtension_additive : (integralScalarExtension R).Additive where
  map_add {X Y f g} := by
    let : Module ℤ R := Module.compHom R (Int.castRingHom R)
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change (1 : R) ⊗ₜ[ℤ, Int.castRingHom R] ((f + g) x) =
      (1 : R) ⊗ₜ[ℤ, Int.castRingHom R] (f x) +
        (1 : R) ⊗ₜ[ℤ, Int.castRingHom R] (g x)
    exact TensorProduct.tmul_add _ _ _

/-- Tensor extension of actual integral singular chains gives the existing
singular chain complex with coefficients in `R`. -/
def integralScalarSingularChainsIso (X : TopCat.{0}) :
    ((integralScalarExtension R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) ≅ Cohomology.Singular.Evaluation.singularScalarChains (R := R) X :=
  AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles.coefficientFunctorChainsIso (integralScalarExtension R)
    (ModuleCat.of ℤ ℤ) (ModuleCat.of R R) (IntegralScalarUnit.integralScalarUnitIso R)
    (TopCat.toSSet.obj X)

@[reassoc]
theorem integralScalarSingularChainsIso_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    ((integralScalarExtension R).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f) ≫ (integralScalarSingularChainsIso R Y).hom =
      (integralScalarSingularChainsIso R X).hom ≫ Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f :=
  AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles.coefficientFunctorChainsIso_hom_naturality (integralScalarExtension R)
    (ModuleCat.of ℤ ℤ) (ModuleCat.of R R) (IntegralScalarUnit.integralScalarUnitIso R) (TopCat.toSSet.map f)

@[simp]
theorem integralScalarSingularChainsIso_hom_one_tmul_simplex
    (X : TopCat.{0}) (n : ℕ) (s : Cohomology.Singular.Basic.singularSimplices X n) :
    (integralScalarSingularChainsIso R X).hom.f n
        ((1 : R) ⊗ₜ[ℤ, Int.castRingHom R]
          Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) s) =
      Cohomology.Singular.ChainDual.simplexChain (R := R) (TopCat.toSSet.obj X) s := by
  have h := ConcreteCategory.congr_hom
    (AlgebraicGeometry.CycleClass.Geometric.RationalSingularChains.Cycles.coefficientFunctorChainsIso_ι (integralScalarExtension R)
      (ModuleCat.of ℤ ℤ) (ModuleCat.of R R) (IntegralScalarUnit.integralScalarUnitIso R)
      (TopCat.toSSet.obj X) n s)
    ((1 : R) ⊗ₜ[ℤ, Int.castRingHom R] (1 : ℤ))
  change (integralScalarSingularChainsIso R X).hom.f n
      ((integralScalarExtension R).map
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s)
          ((1 : R) ⊗ₜ[ℤ, Int.castRingHom R] (1 : ℤ))) =
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R) s
      ((IntegralScalarUnit.integralScalarUnitIso R).hom ((1 : R) ⊗ₜ[ℤ, Int.castRingHom R] (1 : ℤ))) at h
  rw [IntegralScalarUnit.integralScalarUnitIso_hom_tmul] at h
  simpa only [Int.cast_one, mul_one] using! h

@[simp]
theorem integralScalarSingularChainsIso_inv_simplex
    (X : TopCat.{0}) (n : ℕ) (s : Cohomology.Singular.Basic.singularSimplices X n) :
    (integralScalarSingularChainsIso R X).inv.f n
        (Cohomology.Singular.ChainDual.simplexChain (R := R) (TopCat.toSSet.obj X) s) =
      (1 : R) ⊗ₜ[ℤ, Int.castRingHom R]
        Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) s := by
  rw [← integralScalarSingularChainsIso_hom_one_tmul_simplex R X n s]
  exact ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (integralScalarSingularChainsIso R X).hom_inv_id n) _

/-- Transport an actual integral singular-chain map by tensor extension. -/
def scalarExtendSingularMap {X Y : TopCat.{0}}
    (f : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X ⟶ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains Y) :
    Cohomology.Singular.Evaluation.singularScalarChains (R := R) X ⟶ Cohomology.Singular.Evaluation.singularScalarChains (R := R) Y :=
  (integralScalarSingularChainsIso R X).inv ≫
    ((integralScalarExtension R).mapHomologicalComplex (ComplexShape.down ℕ)).map f ≫
      (integralScalarSingularChainsIso R Y).hom

@[simp]
theorem scalarExtendSingularMap_id (X : TopCat.{0}) :
    scalarExtendSingularMap R (𝟙 (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X)) = 𝟙 _ := by
  simp [scalarExtendSingularMap]

@[reassoc (attr := simp)]
theorem scalarExtendSingularMap_comp {X Y Z : TopCat.{0}}
    (f : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X ⟶ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains Y)
    (g : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains Y ⟶ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains Z) :
    scalarExtendSingularMap R (f ≫ g) =
      scalarExtendSingularMap R f ≫ scalarExtendSingularMap R g := by
  simp [scalarExtendSingularMap]

@[simp]
theorem scalarExtendSingularMap_continuous {X Y : TopCat.{0}} (f : X ⟶ Y) :
    scalarExtendSingularMap R (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f) =
      Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f := by
  rw [scalarExtendSingularMap, integralScalarSingularChainsIso_naturality]
  simp

/-- Transport an actual chain homotopy using the additive tensor functor
and the genuine singular-chain comparison isomorphisms. -/
def scalarExtendSingularHomotopy {X Y : TopCat.{0}}
    {f g : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X ⟶ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains Y} (h : Homotopy f g) :
    Homotopy (scalarExtendSingularMap R f) (scalarExtendSingularMap R g) :=
  ((integralScalarExtension R).mapHomotopy h).compLeft
    (integralScalarSingularChainsIso R X).inv |>.compRight
      (integralScalarSingularChainsIso R Y).hom

@[simp]
theorem scalarExtendSingularHomotopy_hom {X Y : TopCat.{0}}
    {f g : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X ⟶ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains Y}
    (h : Homotopy f g) (i j : ℕ) :
    (scalarExtendSingularHomotopy R h).hom i j =
      (integralScalarSingularChainsIso R X).inv.f i ≫
        (integralScalarExtension R).map (h.hom i j) ≫
          (integralScalarSingularChainsIso R Y).hom.f j := by
  simp [scalarExtendSingularHomotopy]

/-- Tensor transport preserves the naturality equation of homotopy
components under a continuous map. -/
theorem scalarExtendSingularHomotopy_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    {uX vX : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X ⟶ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X}
    {uY vY : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains Y ⟶ AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains Y}
    (hX : Homotopy uX vX) (hY : Homotopy uY vY)
    (hnat : ∀ i j, (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f).f i ≫ hY.hom i j =
      hX.hom i j ≫ (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f).f j) (i j : ℕ) :
    (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f).f i ≫
        (scalarExtendSingularHomotopy R hY).hom i j =
      (scalarExtendSingularHomotopy R hX).hom i j ≫
        (Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) f).f j := by
  rw [← scalarExtendSingularMap_continuous R f]
  simp only [scalarExtendSingularMap, scalarExtendSingularHomotopy_hom,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, Category.assoc,
    ← HomologicalComplex.comp_f_assoc, Iso.hom_inv_id,
    HomologicalComplex.id_f, Category.id_comp]
  rw [← Functor.map_comp_assoc, hnat, Functor.map_comp_assoc]

end

end OAI.AlgebraicTopology.Products.SingularChainScalarExtension
