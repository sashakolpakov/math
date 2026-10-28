import OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.PointGenerator
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.DiskGenerator
import OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.HalfChains

/-! # Point Generator -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.PointGenerator

noncomputable section

/-! The actual projected rational point chain is the original rational
complex local generator in dimension zero. -/

open _root_.CategoryTheory
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def complexZeroRationalPointCycle :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of (Fin 0 → ℂ)) ({0}ᶜ)) 0 :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeChainsIso (TopCat.of (Fin 0 → ℂ)) ({0}ᶜ)).hom 0
    (AlgebraicTopology.Duality.Poincare.RationalizedChainClasses.Cycles.rationalizedChainCycle (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of (Fin 0 → ℂ)) ({0}ᶜ))
      0 1 (Relative.PointGenerator.integralRelativePointCycle (TopCat.of (Fin 0 → ℂ)) ({0}ᶜ) 0))

theorem complexZeroRationalPointCycle_val :
    complexZeroRationalPointCycle.val =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of (Fin 0 → ℂ)) ({0}ᶜ)).f 0
        (Singular.CrossBoundary.scalarPointChain ℚ (TopCat.of (Fin 0 → ℂ)) 0) := by
  have h := AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison.rationalRelativeChainsIso_one_tmul_projection (TopCat.of (Fin 0 → ℂ)) ({0}ᶜ) 0
    (CircleArcWinding.integralPointChain (TopCat.of (Fin 0 → ℂ)) 0)
  change complexZeroRationalPointCycle.val =
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of (Fin 0 → ℂ)) ({0}ᶜ)).f 0
      (ChainRepresentatives.rationalSingularChainElement (TopCat.of (Fin 0 → ℂ)) 0
        (CircleArcWinding.integralPointChain (TopCat.of (Fin 0 → ℂ)) 0)) at h
  rw [CircleArcWinding.integralPointChain, Axis.HalfChains.rationalSingularChainElement_simplex] at h
  exact h

def complexZeroRationalPointClass : CycleClass.Geometric.RelativeScalarChains.Cycles.localScalarHomology ℚ (TopCat.of (Fin 0 → ℂ)) 0 0 :=
  AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ 0 complexZeroRationalPointCycle

theorem complexZeroRationalPointClass_coordinate :
    (CycleClass.Geometric.RationalRelativeHomology.Cycles.complexNormalRationalTopLocalHomologyIso 0).hom complexZeroRationalPointClass = 1 := by
  change CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeUnitIso.hom
    (CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules.map (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 0).hom
      ((CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso (TopCat.of (Fin 0 → ℂ)) ({0}ᶜ) 0).hom
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of (Fin 0 → ℂ)) ({0}ᶜ)) 0
          (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeChainsIso (TopCat.of (Fin 0 → ℂ)) ({0}ᶜ)).hom 0
            (AlgebraicTopology.Duality.Poincare.RationalizedChainClasses.Cycles.rationalizedChainCycle (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of (Fin 0 → ℂ)) ({0}ᶜ)) 0 1
              (Relative.PointGenerator.integralRelativePointCycle (TopCat.of (Fin 0 → ℂ)) ({0}ᶜ) 0)))))) = 1
  rw [AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison.rationalRelativeHomologyIso_chainClass]
  change CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeUnitIso.hom ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ]
    (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 0).hom
      (Relative.PointGenerator.integralRelativePointClass (TopCat.of (Fin 0 → ℂ)) ({0}ᶜ) 0)) = 1
  rw [Relative.PointGenerator.integralRelativePointClass_complexZero_coordinate, CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeUnitIso_hom_one_tmul]
  rfl

theorem complexZeroRationalPointClass_eq_originalGenerator :
    complexZeroRationalPointClass = CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator 0 := by
  apply (CycleClass.Geometric.RationalRelativeHomology.Cycles.complexNormalRationalTopLocalHomologyIso 0).toLinearEquiv.injective
  change (CycleClass.Geometric.RationalRelativeHomology.Cycles.complexNormalRationalTopLocalHomologyIso 0).hom _ = (CycleClass.Geometric.RationalRelativeHomology.Cycles.complexNormalRationalTopLocalHomologyIso 0).hom _
  rw [complexZeroRationalPointClass_coordinate]
  exact (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator_normalization 0).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.PointGenerator
