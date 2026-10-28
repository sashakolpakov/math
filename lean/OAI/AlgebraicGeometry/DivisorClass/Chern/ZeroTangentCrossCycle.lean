import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.PointGenerator
import OAI.AlgebraicGeometry.DivisorClass.Chern.RightPointProjectionFilling
import OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.CrossFilling
import OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.FactorCrossCycle
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalProductGenerator

/-! # Zero Tangent Cross Cycle -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ZeroTangentCrossCycle

noncomputable section

section

/-! The actual local cross generator when the tangent space is a point,
with its original quotient-chain representative. -/

open _root_.CategoryTheory _root_.HomologicalComplex
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalProductGenerator.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def relativeCycleChangeSupport (X : TopCat.{0}) (A B : Set X) (h : A = B) (n : ℕ)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) n) : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X B) n :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (eqToHom (congrArg (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X) h)) n z

theorem relativeCycleChangeSupport_projection (X : TopCat.{0}) (A B : Set X) (h : A = B) (n : ℕ)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) n) (b : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X n)
    (hz : z.val = (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A).f n b) :
    (relativeCycleChangeSupport X A B h n z).val = (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X B).f n b := by
  subst B
  exact hz

def zeroTangentCrossCycle :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of ((Fin 1 → ℂ) × (Fin 0 → ℂ))) ({0}ᶜ)) 2 :=
  relativeCycleChangeSupport (TopCat.of ((Fin 1 → ℂ) × (Fin 0 → ℂ)))
    (HodgeConjecture.DegreeTwo.RelativeCrossSupport.Constructions.crossSupportComplement (TopCat.of (Fin 1 → ℂ)) (TopCat.of (Fin 0 → ℂ)) ({0}ᶜ) ({0}ᶜ)) ({0}ᶜ)
    (HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing.Constructions.crossSupportComplement_punctures (TopCat.of (Fin 1 → ℂ)) (TopCat.of (Fin 0 → ℂ)) 0 0) 2
    (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross ℚ (TopCat.of (Fin 1 → ℂ)) (TopCat.of (Fin 0 → ℂ))
      ({0}ᶜ) ({0}ᶜ)) 2
      (DiskTensorCycle.diskTensorCycle (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of (Fin 1 → ℂ)) ({0}ᶜ))
        (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of (Fin 0 → ℂ)) ({0}ᶜ)) 0
        Rational.DiskGenerator.normalSupportedDiskRationalCycle Rational.PointGenerator.complexZeroRationalPointCycle))

theorem zeroTangentCrossCycle_val :
    zeroTangentCrossCycle.val =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of ((Fin 1 → ℂ) × (Fin 0 → ℂ))) ({0}ᶜ)).f 2
        (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (Fin 1 → ℂ)) (TopCat.of (Fin 0 → ℂ)) 2 0 2 rfl
          Rational.DiskGenerator.normalSupportedDiskRationalFilling (Singular.CrossBoundary.scalarPointChain ℚ (TopCat.of (Fin 0 → ℂ)) 0)) := by
  unfold zeroTangentCrossCycle
  apply relativeCycleChangeSupport_projection
  change (HodgeConjecture.DegreeTwo.RelativeCrossProduct.Constructions.relativeSingularChainCross ℚ (TopCat.of (Fin 1 → ℂ)) (TopCat.of (Fin 0 → ℂ)) ({0}ᶜ) ({0}ᶜ)).f 2
    (ιTensorObj (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of (Fin 1 → ℂ)) ({0}ᶜ))
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of (Fin 0 → ℂ)) ({0}ᶜ)) 2 0 2 rfl
      (Rational.DiskGenerator.normalSupportedDiskRationalCycle.val ⊗ₜ[ℚ] Rational.PointGenerator.complexZeroRationalPointCycle.val)) = _
  rw [Rational.DiskGenerator.normalSupportedDiskRationalCycle_val, Rational.PointGenerator.complexZeroRationalPointCycle_val]
  exact Relative.CrossRepresentatives.relativeSingularCross_quotient_representatives (TopCat.of (Fin 1 → ℂ)) (TopCat.of (Fin 0 → ℂ))
    ({0}ᶜ) ({0}ᶜ) 2 0 Rational.DiskGenerator.normalSupportedDiskRationalFilling (Singular.CrossBoundary.scalarPointChain ℚ (TopCat.of (Fin 0 → ℂ)) 0)

theorem localProductCrossGenerator_zeroTangent :
    HodgeConjecture.DegreeTwo.LocalProductGenerator.Constructions.localProductCrossGenerator 1 0 =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of ((Fin 1 → ℂ) × (Fin 0 → ℂ))) ({0}ᶜ)) 2
        zeroTangentCrossCycle := by
  have h := Relative.CrossFilling.relativeDiskCrossClass_eq_filling (TopCat.of (Fin 1 → ℂ)) (TopCat.of (Fin 0 → ℂ))
    ({0}ᶜ) ({0}ᶜ) ({0}ᶜ)
    (HodgeConjecture.DegreeTwo.RelativeCrossNonvanishing.Constructions.crossSupportComplement_punctures (TopCat.of (Fin 1 → ℂ)) (TopCat.of (Fin 0 → ℂ)) 0 0)
    0 Rational.DiskGenerator.normalSupportedDiskRationalFilling (Singular.CrossBoundary.scalarPointChain ℚ (TopCat.of (Fin 0 → ℂ)) 0)
    Rational.DiskGenerator.normalSupportedDiskRationalCycle Rational.PointGenerator.complexZeroRationalPointCycle
    Rational.DiskGenerator.normalSupportedDiskRationalCycle_val Rational.PointGenerator.complexZeroRationalPointCycle_val zeroTangentCrossCycle zeroTangentCrossCycle_val
  have hx : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of (Fin 1 → ℂ)) ({0}ᶜ)) 2
      Rational.DiskGenerator.normalSupportedDiskRationalCycle = CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator 1 :=
    Rational.DiskGenerator.normalSupportedDiskRationalClass_eq_originalGenerator
  have hy : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of (Fin 0 → ℂ)) ({0}ᶜ)) 0
      Rational.PointGenerator.complexZeroRationalPointCycle = CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator 0 :=
    Rational.PointGenerator.complexZeroRationalPointClass_eq_originalGenerator
  rw [hx, hy] at h
  exact h

end

/-! The existing local cross generator with a zero-dimensional tangent
factor projects to the original complex normal-line generator. -/

open _root_.CategoryTheory _root_.HomologicalComplex
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LocalProductGenerator.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def zeroTangentComplexCoordinates :
    ((Fin 1 → ℂ) × (Fin 0 → ℂ)) ≃L[ℂ] (Fin 1 → ℂ) where
  toFun := Prod.fst
  invFun x := (x, 0)
  left_inv _ := Prod.ext rfl (Subsingleton.elim _ _)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_fst
  continuous_invFun := continuous_id.prodMk continuous_const

theorem zeroTangentProjection_puncture :
    Set.MapsTo (TopCat.prodFst (X := TopCat.of (Fin 1 → ℂ)) (Y := TopCat.of (Fin 0 → ℂ)))
      ({0}ᶜ) ({0}ᶜ : Set (Fin 1 → ℂ)) := by
  intro x hx he
  exact hx (Prod.ext he (Subsingleton.elim _ _))

theorem zeroTangentCrossCycle_projected :
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ
      (TopCat.prodFst (X := TopCat.of (Fin 1 → ℂ)) (Y := TopCat.of (Fin 0 → ℂ)))
      zeroTangentProjection_puncture) 2 zeroTangentCrossCycle =
      RightPointProjectionFilling.unitRightPointRelativeFillingCycle NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 1
        Rational.DiskGenerator.normalSupportedDiskRationalFilling Rational.DiskGenerator.normalOrthantCircleRationalCycle
        Rational.DiskGenerator.normalSupportedDiskRationalFilling_boundary := by
  apply Subtype.ext
  rw [Complex.FactorCrossCycle.relativeCycleMap_projection _ zeroTangentProjection_puncture 2 zeroTangentCrossCycle _ zeroTangentCrossCycle_val]
  have h := ConcreteCategory.congr_hom (congrArg (fun f => f.f 2)
    (RightPointProjectionFilling.singularRightPointCross_projection (TopCat.of (Fin 1 → ℂ)) (TopCat.of (Fin 0 → ℂ)) 0))
    Rational.DiskGenerator.normalSupportedDiskRationalFilling
  exact congrArg ((CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured).f 2) h

theorem zeroTangentCrossGenerator_projection :
    homologyMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ
      (TopCat.prodFst (X := TopCat.of (Fin 1 → ℂ)) (Y := TopCat.of (Fin 0 → ℂ)))
      zeroTangentProjection_puncture) 2 (HodgeConjecture.DegreeTwo.LocalProductGenerator.Constructions.localProductCrossGenerator 1 0) =
      CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopHomologyGenerator 1 := by
  rw [localProductCrossGenerator_zeroTangent, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality, zeroTangentCrossCycle_projected,
    RightPointProjectionFilling.unitRightPointRelativeFillingCycle_class]
  have hc : Relative.FillingCycle.relativeFillingCycle ℚ NormalWinding.windingNormalLine NormalWinding.windingNormalPunctured 1
      Rational.DiskGenerator.normalSupportedDiskRationalFilling Rational.DiskGenerator.normalOrthantCircleRationalCycle
      Rational.DiskGenerator.normalSupportedDiskRationalFilling_boundary = Rational.DiskGenerator.normalSupportedDiskRationalCycle :=
    Subtype.ext Rational.DiskGenerator.normalSupportedDiskRationalCycle_val.symm
  rw [hc]
  exact Rational.DiskGenerator.normalSupportedDiskRationalClass_eq_originalGenerator

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ZeroTangentCrossCycle
