import OAI.AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains
import Mathlib.Basic.Complex.Basic

/-! # Relative Coefficients -/

namespace OAI.AlgebraicTopology.FundamentalClass.RelativeCoefficients.IntegrationConstruction

noncomputable section

/-! Change the coefficients of genuine relative chains and relative homology
from integers to complex numbers, with the actual projection formula. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles OAI.AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def integerLinear {V W : Type} [AddCommGroup V] [AddCommGroup W]
    {modV : Module ℤ V} {modW : Module ℤ W} (f : V →+ W) : V →ₗ[ℤ] W where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    change f (modV.smul r x) = modW.smul r (f x)
    simp only [int_smul_eq_zsmul, map_zsmul]

def descendLinearMap {R : Type} [Ring R]
    {V W P : Type} [AddCommGroup V] [AddCommGroup W] [AddCommGroup P]
    {modV : Module R V} {modW : Module R W} {modP : Module R P}
    (π : V →ₗ[R] W) (hπ : Function.Surjective π) (f : V →ₗ[R] P)
    (hf : LinearMap.ker π ≤ LinearMap.ker f) : W →ₗ[R] P :=
  ((LinearMap.ker π).liftQ f hf).comp (π.quotKerEquivOfSurjective hπ).symm.toLinearMap

theorem descendLinearMap_apply {R : Type} [Ring R]
    {V W P : Type} [AddCommGroup V] [AddCommGroup W] [AddCommGroup P]
    {modV : Module R V} {modW : Module R W} {modP : Module R P}
    (π : V →ₗ[R] W) (hπ : Function.Surjective π) (f : V →ₗ[R] P)
    (hf : LinearMap.ker π ≤ LinearMap.ker f) (v : V) :
    descendLinearMap π hπ f hf (π v) = f v := by
  simp only [descendLinearMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

def relativeCoefficientBeforeQuotient (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n →ₗ[ℤ] (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℂ X A).X n :=
  integerLinear (((AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℂ X A).f n).hom.toAddMonoidHom.comp
    (Duality.Poincare.IntegralCapCoefficients.integralToScalarSingular (R := ℂ) X n).toAddMonoidHom)

theorem relativeCoefficientBeforeQuotient_kernel (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    LinearMap.ker ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n).hom ≤
      LinearMap.ker (relativeCoefficientBeforeQuotient X A n) := by
  rw [show LinearMap.ker ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n).hom =
      LinearMap.range ((AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℤ X A).f n).hom from
    AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection_ker ℤ X A n]
  rintro _ ⟨z, rfl⟩
  change (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℂ X A).f n
    (Duality.Poincare.IntegralCapCoefficients.integralToScalarSingular (R := ℂ) X n
      ((AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℤ X A).f n z)) = 0
  have hn := Duality.Poincare.IntegralCapCoefficients.integralToScalarSimplicial_naturality (R := ℂ)
    (TopCat.toSSet.map (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A)) n z
  change (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℂ X A).f n
    (Duality.Poincare.IntegralCapCoefficients.integralToScalarSingular (R := ℂ) (TopCat.of A) n z) =
    Duality.Poincare.IntegralCapCoefficients.integralToScalarSingular (R := ℂ) X n ((AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℤ X A).f n z) at hn
  rw [← hn]
  exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion_projection ℂ X A) n)
    (Duality.Poincare.IntegralCapCoefficients.integralToScalarSingular (R := ℂ) (TopCat.of A) n z)

def relativeCoefficient (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X n →ₗ[ℤ] (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℂ X A).X n :=
  descendLinearMap ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n).hom
    (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection_surjective ℤ X A n)
    (relativeCoefficientBeforeQuotient X A n) (relativeCoefficientBeforeQuotient_kernel X A n)

theorem relativeCoefficient_projection (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    relativeCoefficient X A n ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n z) =
      (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℂ X A).f n (Duality.Poincare.IntegralCapCoefficients.integralToScalarSingular (R := ℂ) X n z) := by
  rw [relativeCoefficient, descendLinearMap_apply]
  rfl

theorem relativeCoefficient_d (X : TopCat.{0}) (A : Set X) (i j : ℕ)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X i) :
    relativeCoefficient X A j ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).d i j z) =
      (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℂ X A).d i j (relativeCoefficient X A i z) := by
  obtain ⟨z, rfl⟩ := AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection_surjective ℤ X A i z
  have h := ConcreteCategory.congr_hom ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).comm i j) z
  change (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).d i j ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f i z) =
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f j ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d i j z) at h
  change relativeCoefficient X A j
    ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).d i j ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f i z)) =
    (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℂ X A).d i j
      (relativeCoefficient X A i ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f i z))
  rw [h, relativeCoefficient_projection, relativeCoefficient_projection]
  have hd : Duality.Poincare.IntegralCapCoefficients.integralToScalarSingular (R := ℂ) X j ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d i j z) =
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℂ) X).d i j (Duality.Poincare.IntegralCapCoefficients.integralToScalarSingular (R := ℂ) X i z) :=
    Duality.Poincare.IntegralCapCoefficients.integralToScalarSimplicial_d (R := ℂ) (TopCat.toSSet.obj X) i j z
  rw [hd]
  exact (ConcreteCategory.congr_hom ((AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℂ X A).comm i j)
    (Duality.Poincare.IntegralCapCoefficients.integralToScalarSingular (R := ℂ) X i z)).symm

def relativeCoefficientCycles (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n →ₗ[ℤ]
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℂ X A) n :=
  integerLinear
    { toFun z := ⟨relativeCoefficient X A n z.val, by
        change (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℂ X A).d n ((ComplexShape.down ℕ).next n)
          (relativeCoefficient X A n z.val) = 0
        rw [← relativeCoefficient_d, Cohomology.Singular.ChainRepresentatives.chainCycle_d_eq_zero, map_zero]⟩
      map_zero' := by apply Subtype.ext; exact map_zero _
      map_add' z w := by apply Subtype.ext; exact map_add _ _ _ }

def relativeCoefficientHomology (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).homology n →ₗ[ℤ] (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℂ X A).homology n :=
  descendLinearMap (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n)
    (Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n)
    (integerLinear ((Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℂ X A) n).toAddMonoidHom.comp
      (relativeCoefficientCycles X A n).toAddMonoidHom)) (by
        intro z hz
        obtain ⟨w, hw⟩ := (Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n z).mp hz
        change Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℂ X A) n (relativeCoefficientCycles X A n z) = 0
        apply (Cohomology.Singular.ChainRepresentatives.chainClass_eq_zero_iff_exists _ n _).mpr
        refine ⟨relativeCoefficient X A (n + 1) w, ?_⟩
        rw [← relativeCoefficient_d, hw]
        rfl)

theorem relativeCoefficientHomology_class (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n) :
    relativeCoefficientHomology X A n (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) n z) =
      Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℂ X A) n (relativeCoefficientCycles X A n z) := by
  rw [relativeCoefficientHomology, descendLinearMap_apply]
  rfl

theorem relativeCoefficientCycles_projection (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) n) :
    relativeCoefficientCycles X A n (Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A) n z) =
      Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℂ X A) n
        (Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularCycles (R := ℂ) X n z) := by
  apply Subtype.ext
  exact relativeCoefficient_projection X A n z.val

theorem relativeCoefficientHomology_projection (X : TopCat.{0}) (A : Set X) (n : ℕ)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology n) :
    relativeCoefficientHomology X A n
      (HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A) n z) =
      HomologicalComplex.homologyMap (AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℂ X A) n
        (Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℂ) X n z) := by
  obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) n z
  rw [Cohomology.Singular.EvaluationNaturality.chainClass_naturality, relativeCoefficientHomology_class,
    Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology_chainClass, Cohomology.Singular.EvaluationNaturality.chainClass_naturality,
    relativeCoefficientCycles_projection]

end

end OAI.AlgebraicTopology.FundamentalClass.RelativeCoefficients.IntegrationConstruction
