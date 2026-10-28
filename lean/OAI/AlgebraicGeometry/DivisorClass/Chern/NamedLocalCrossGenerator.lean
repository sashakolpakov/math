import OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.FactorCrossCycle
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalProductGenerator

/-! # Named Local Cross Generator -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.NamedLocalCrossGenerator

noncomputable section

/-! The existing named local cross generator is the actual factorwise
disk cross filling, with only its displayed degree reindexed. -/

open _root_.CategoryTheory _root_.HomologicalComplex
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalProductGenerator.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def tangentOriginalGeneratorCycle (p : ℕ) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ)) (2 * (p + 1)) := by
  simpa only [Nat.mul_succ] using Rational.PositiveComplexSphere.positiveComplexOrthantRationalCycle p

def tangentOriginalGeneratorFilling (p : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (Fin (p + 1) → ℂ))).X (2 * (p + 1)) := by
  simpa only [Nat.mul_succ] using Rational.PositiveComplexSphere.positiveComplexRationalFilling p

theorem tangentOriginalGeneratorCycle_val (p : ℕ) :
    (tangentOriginalGeneratorCycle p).val =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ)).f (2 * (p + 1))
        (tangentOriginalGeneratorFilling p) := by
  simpa only [tangentOriginalGeneratorCycle, tangentOriginalGeneratorFilling,
    Rational.PositiveComplexSphere.positiveComplexRationalFilling, Nat.mul_succ, id_eq] using Rational.PositiveComplexSphere.positiveComplexOrthantRationalCycle_val p

theorem tangentOriginalGeneratorCycle_class (p : ℕ) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ)) (2 * (p + 1))
      (tangentOriginalGeneratorCycle p) = CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator (p + 1) := by
  simpa only [tangentOriginalGeneratorCycle, Rational.PositiveComplexSphere.positiveComplexOrthantRationalClass,
    Nat.mul_succ, id_eq] using Rational.PositiveComplexSphere.positiveComplexOrthantRationalClass_eq_originalGenerator p

def lineTangentCrossClass (p : ℕ) :
    CycleClass.Geometric.RelativeScalarChains.Cycles.localScalarHomology ℚ (TopCat.of ((Fin 1 → ℂ) × (Fin (p + 1) → ℂ))) 0 (2 * p + 4) :=
  eqToHom (congrArg (CycleClass.Geometric.RelativeScalarChains.Cycles.localScalarHomology ℚ
    (TopCat.of ((Fin 1 → ℂ) × (Fin (p + 1) → ℂ))) 0)
    (show 2 * 1 + 2 * (p + 1) = 2 * p + 4 by omega))
    (HodgeConjecture.DegreeTwo.LocalProductGenerator.Constructions.localProductCrossGenerator 1 (p + 1))

theorem lineTangentCrossClass_eq_cycle (p : ℕ) :
    lineTangentCrossClass p = AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ
      (TopCat.of ((Fin 1 → ℂ) × (Fin (p + 1) → ℂ))) ({0}ᶜ)) (2 * p + 4) (Complex.FactorCrossCycle.complexFactorCrossCycle p) := by
  have hz : (Complex.FactorCrossCycle.complexFactorCrossCycle p).val =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of ((Fin 1 → ℂ) × (Fin (p + 1) → ℂ))) ({0}ᶜ)).f (2 * p + 4)
        (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (Fin 1 → ℂ)) (TopCat.of (Fin (p + 1) → ℂ))
          2 (2 * (p + 1)) (2 * p + 4) (by omega)
          Rational.DiskGenerator.normalSupportedDiskRationalFilling (tangentOriginalGeneratorFilling p)) := by
    simpa only [tangentOriginalGeneratorFilling, Nat.mul_succ, id_eq] using Complex.FactorCrossCycle.complexFactorCrossCycle_val p
  have h := Relative.CrossFilling.relativeDiskCrossClass_eq_filling_at
    (TopCat.of (Fin 1 → ℂ)) (TopCat.of (Fin (p + 1) → ℂ)) ({0}ᶜ) ({0}ᶜ) ({0}ᶜ)
    (HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing.Constructions.crossSupportComplement_punctures (TopCat.of (Fin 1 → ℂ)) (TopCat.of (Fin (p + 1) → ℂ)) 0 0)
    (2 * (p + 1)) (2 * p + 4) (by omega)
    Rational.DiskGenerator.normalSupportedDiskRationalFilling (tangentOriginalGeneratorFilling p)
    Rational.DiskGenerator.normalSupportedDiskRationalCycle (tangentOriginalGeneratorCycle p)
    Rational.DiskGenerator.normalSupportedDiskRationalCycle_val (tangentOriginalGeneratorCycle_val p)
    (Complex.FactorCrossCycle.complexFactorCrossCycle p) hz
  have hx : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of (Fin 1 → ℂ)) ({0}ᶜ)) 2
      Rational.DiskGenerator.normalSupportedDiskRationalCycle = CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator 1 :=
    Rational.DiskGenerator.normalSupportedDiskRationalClass_eq_originalGenerator
  rw [tangentOriginalGeneratorCycle_class, hx] at h
  exact h

theorem lineTangentCrossClass_line (p : ℕ) :
    homologyMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (Complex.ProductFactorMaps.complexProductLineMap p) (Complex.ProductFactorMaps.complexProductLineMap_puncture p))
      (2 * p + 4) (lineTangentCrossClass p) = CombinedComplexSphereMap.combinedComplexRationalGeneratorClass p := by
  rw [lineTangentCrossClass_eq_cycle, Complex.FactorCrossCycle.complexFactorCrossCycle_line_class,
    Complex.DiskProductGenerator.complexDiskProductFillingClass_eq_generatorClass]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.NamedLocalCrossGenerator
