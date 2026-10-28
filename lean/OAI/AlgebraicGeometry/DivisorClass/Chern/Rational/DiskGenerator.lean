import OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.DiskGenerator
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ChainRepresentatives

/-! # Disk Generator -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.DiskGenerator

noncomputable section

/-!
# ChernClass: the supported disk represents the original rational normal generator

Coefficient change preserves the displayed disk, its boundary, and its
relative class. The native rationalization isomorphism carries its unit
integral coordinate to the rational unit.
-/

open _root_.CategoryTheory
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def normalSupportedDiskRationalFilling : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) NormalWinding.windingNormalLine).X 2 :=
  ChainRepresentatives.rationalSingularChainElement NormalWinding.windingNormalLine 2 Complex.DiskGenerator.normalSupportedDiskFilling

def normalOrthantCircleRationalCycle :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of NormalWinding.windingNormalPunctured)) 1 :=
  ChainRepresentatives.rationalSingularCycle (TopCat.of NormalWinding.windingNormalPunctured) 1 Complex.DiskGenerator.normalOrthantCircleCycle

theorem normalSupportedDiskRationalFilling_boundary :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) NormalWinding.windingNormalLine).d 2 1 normalSupportedDiskRationalFilling =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured).f 1
        normalOrthantCircleRationalCycle.val := by
  rw [normalSupportedDiskRationalFilling, ChainRepresentatives.rationalSingularChainElement_d,
    Complex.DiskGenerator.normalSupportedDiskFilling_boundary]
  exact (ChainRepresentatives.rationalSingularChainElement_map
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured) 1 Complex.DiskGenerator.normalOrthantCircleCycle.val).symm

def normalSupportedDiskRationalCycle :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured) 2 :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeChainsIso NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured).hom 2
    (AlgebraicTopology.Duality.Poincare.RationalizedChainClasses.Cycles.rationalizedChainCycle (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured)
      2 1 Complex.DiskGenerator.normalSupportedDiskRelativeCycle)

theorem normalSupportedDiskRationalCycle_val :
    normalSupportedDiskRationalCycle.val =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured).f 2
        normalSupportedDiskRationalFilling :=
  AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison.rationalRelativeChainsIso_one_tmul_projection NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 2
    Complex.DiskGenerator.normalSupportedDiskFilling

def normalSupportedDiskRationalClass : CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomology ℚ NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 2 :=
  AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured) 2 normalSupportedDiskRationalCycle

theorem normalSupportedDiskRationalClass_coordinate :
    (CycleClass.Geometric.RationalRelativeHomology.Cycles.complexNormalRationalTopLocalHomologyIso 1).hom normalSupportedDiskRationalClass = 1 := by
  change CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeUnitIso.hom
    (CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeModules.map (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).hom
      ((CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeHomologyIso NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 2).hom
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured) 2
          (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.RationalRelativeHomology.Cycles.rationalRelativeChainsIso NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured).hom 2
            (AlgebraicTopology.Duality.Poincare.RationalizedChainClasses.Cycles.rationalizedChainCycle (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured)
              2 1 Complex.DiskGenerator.normalSupportedDiskRelativeCycle))))) = 1
  rw [AlgebraicTopology.Duality.Poincare.RelativeRationalEvaluationComparison.rationalRelativeHomologyIso_chainClass]
  change CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeUnitIso.hom ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ]
    (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso 1).hom Complex.DiskGenerator.normalSupportedDiskRelativeClass) = 1
  rw [Complex.DiskGenerator.normalSupportedDiskRelativeClass_eq_originalGenerator, Iso.inv_hom_id_apply,
    CycleClass.Geometric.RationalScalarExtension.Cycles.rationalizeUnitIso_hom_one_tmul]
  rfl

theorem normalSupportedDiskRationalClass_eq_originalGenerator :
    normalSupportedDiskRationalClass = CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator 1 := by
  apply (CycleClass.Geometric.RationalRelativeHomology.Cycles.complexNormalRationalTopLocalHomologyIso 1).toLinearEquiv.injective
  change (CycleClass.Geometric.RationalRelativeHomology.Cycles.complexNormalRationalTopLocalHomologyIso 1).hom normalSupportedDiskRationalClass =
    (CycleClass.Geometric.RationalRelativeHomology.Cycles.complexNormalRationalTopLocalHomologyIso 1).hom (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator 1)
  rw [normalSupportedDiskRationalClass_coordinate]
  exact (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator_normalization 1).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.DiskGenerator
