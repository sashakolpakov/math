import OAI.AlgebraicTopology.Cohomology.Singular.RelativeSequence
import OAI.AlgebraicTopology.Cohomology.Singular.InjectiveChainDual
import OAI.AlgebraicTopology.Cohomology.Singular.IntegralCoefficientInjective
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Module.LinearMap.Rat

/-! # Relative Cochain Dual -/

namespace OAI.AlgebraicTopology.Duality.Poincare.RelativeCochainDual

noncomputable section

/-!
# Relative rational cochains as the dual of integral relative chains

The quotient and kernel here are the existing categorical complexes defining
relative singular chains and relative singular cochains. The comparison uses
the universal property of that quotient, together with the actual evaluation
of cochains on singular simplices.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Rational coefficients, considered as an actual integer module. -/
abbrev rationalIntegralCoefficient : ModuleCat.{0} ℤ :=
  (ModuleCat.restrictScalars (algebraMap ℤ ℚ)).obj (ModuleCat.of ℚ ℚ)

/-- Contravariant rational-valued additive duality on integral chain complexes. -/
abbrev rationalChainDualFunctor :
    (ChainComplex (ModuleCat.{0} ℤ) ℕ)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{0} ℕ :=
  HomologicalComplex.opFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) ⋙
    (preadditiveYoneda.obj rationalIntegralCoefficient).mapHomologicalComplex
      (ComplexShape.up ℕ)

/-- The actual additive Hom complex of an integral chain complex into `ℚ`. -/
abbrev rationalChainDual (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    CochainComplex AddCommGrpCat.{0} ℕ :=
  rationalChainDualFunctor.obj (op C)

/-- Precomposition with an actual integral chain map. -/
abbrev rationalChainDualMap {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : C ⟶ D) :
    rationalChainDual D ⟶ rationalChainDual C :=
  rationalChainDualFunctor.map f.op

/-- Forget only the scalar structure on a rational cochain complex. -/
abbrev rationalCochainsForget :
    CochainComplex (ModuleCat.{0} ℚ) ℕ ⥤ CochainComplex AddCommGrpCat.{0} ℕ :=
  (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).mapHomologicalComplex (ComplexShape.up ℕ)

/-- Evaluation identifies rational cochains with integer-linear maps on
integral simplicial chains. -/
def rationalSimplicialChainDualEquiv (K : SSet.{0}) (n : ℕ) :
    (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of ℚ ℚ)).X n ≃+
      ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K).X n →ₗ[ℤ] rationalIntegralCoefficient) :=
  (Cohomology.Singular.Coefficients.degreewiseFunctionIso K (ModuleCat.of ℚ ℚ) n).toLinearEquiv.toAddEquiv.trans
    (Cohomology.Singular.ChainDual.functionChainFunctionalEquiv K rationalIntegralCoefficient n).toAddEquiv

@[simp]
theorem rationalSimplicialChainDualEquiv_simplex (K : SSet.{0}) (n : ℕ)
    (c : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of ℚ ℚ)).X n) (s : K _⦋n⦌) :
    rationalSimplicialChainDualEquiv K n c (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) K s) =
      Cohomology.Singular.Coefficients.simplicialEvaluation K (ModuleCat.of ℚ ℚ) s c := by
  change Cohomology.Singular.ChainDual.chainFunctionalOfFunction K rationalIntegralCoefficient n
    ((Cohomology.Singular.Coefficients.degreewiseFunctionIso K (ModuleCat.of ℚ ℚ) n).hom c) (Cohomology.Singular.ChainDual.simplexChain K s) = _
  rw [Cohomology.Singular.ChainDual.chainFunctionalOfFunction_simplex, Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply]

/-- Evaluation intertwines the rational coboundary with the integral boundary. -/
theorem rationalSimplicialChainDualEquiv_d (K : SSet.{0}) (i j : ℕ)
    (c : (Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of ℚ ℚ)).X i) :
    rationalSimplicialChainDualEquiv K j
        ((Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of ℚ ℚ)).d i j c) =
      (rationalSimplicialChainDualEquiv K i c).comp
        ((Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K).d j i).hom := by
  by_cases hij : (ComplexShape.up ℕ).Rel i j
  · have hj : i + 1 = j := hij
    subst j
    apply Cohomology.Singular.ChainDual.chainFunctional_ext K rationalIntegralCoefficient
    intro s
    simp only [rationalSimplicialChainDualEquiv_simplex, LinearMap.comp_apply,
      Cohomology.Singular.ChainDual.simplexChain_boundary, map_sum, map_zsmul]
    exact Cohomology.Singular.Formulas.evaluation_coboundary_apply K (ModuleCat.of ℚ ℚ) c s
  · have hji : ¬ (ComplexShape.down ℕ).Rel j i := hij
    rw [(Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of ℚ ℚ)).shape i j hij,
      (Cohomology.Singular.ChainDual.simplicialScalarChains (R := ℤ) K).shape j i hji]
    simp

/-- Evaluation is compatible with pullback and the integral chain map. -/
theorem rationalSimplicialChainDualEquiv_pullback {K L : SSet.{0}} (f : K ⟶ L)
    (n : ℕ) (c : (Cohomology.Singular.Basic.simplicialCochains L (ModuleCat.of ℚ ℚ)).X n) :
    rationalSimplicialChainDualEquiv K n
        ((Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℚ ℚ) f).f n c) =
      (rationalSimplicialChainDualEquiv L n c).comp
        ((Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℤ) f).f n).hom := by
  apply Cohomology.Singular.ChainDual.chainFunctional_ext K rationalIntegralCoefficient
  intro s
  simp only [rationalSimplicialChainDualEquiv_simplex, LinearMap.comp_apply,
    Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap_simplex]
  exact Cohomology.Singular.Formulas.evaluation_pullback_apply (ModuleCat.of ℚ ℚ) f c s

/-- Ordinary rational singular cochains are the rational-valued additive dual
of the actual integral singular chain complex. -/
def rationalSingularCochainDualIso (X : TopCat.{0}) :
    rationalCochainsForget.obj (Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X) ≅
      rationalChainDual (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => ((rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) n).trans
      ModuleCat.homAddEquiv.symm).toAddCommGrpIso)
    (by
      intro i j _
      apply AddCommGrpCat.ext
      intro c
      apply ModuleCat.hom_ext
      change (rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) i c).comp
          ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d j i).hom =
        rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) j
          ((Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).d i j c)
      exact (rationalSimplicialChainDualEquiv_d (TopCat.toSSet.obj X) i j c).symm)

@[reassoc]
theorem rationalSingularCochainDualIso_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    rationalCochainsForget.map (Cohomology.Singular.Functor.singularPullback (ModuleCat.of ℚ ℚ) f) ≫
        (rationalSingularCochainDualIso X).hom =
      (rationalSingularCochainDualIso Y).hom ≫
        rationalChainDualMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f) := by
  ext n : 1
  apply AddCommGrpCat.ext
  intro c
  apply ModuleCat.hom_ext
  exact rationalSimplicialChainDualEquiv_pullback (TopCat.toSSet.map f) n c

/-- Dualizing an actual cokernel gives a kernel. This uses only the universal
property of Hom, and does not require injective coefficients. -/
def rationalDualCokernelIsKernel {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : C ⟶ D) :
    IsLimit (KernelFork.ofι (rationalChainDualMap (cokernel.π f)) (show
      rationalChainDualMap (cokernel.π f) ≫ rationalChainDualMap f = 0 by
        change rationalChainDualFunctor.map (cokernel.π f).op ≫
          rationalChainDualFunctor.map f.op = 0
        rw [← Functor.map_comp, ← op_comp, cokernel.condition, op_zero,
          Functor.map_zero])) :=
  (KernelFork.ofι (cokernel.π f).op (by
    rw [← op_comp, cokernel.condition, op_zero])).mapIsLimit
      (CokernelCofork.IsColimit.ofπOp (cokernel.π f) (cokernel.condition f)
        (cokernelIsCokernel f)) rationalChainDualFunctor

/-- The canonical dual-of-quotient / kernel-of-restriction isomorphism. -/
def rationalDualCokernelIso {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : C ⟶ D) :
    rationalChainDual (cokernel f) ≅ kernel (rationalChainDualMap f) :=
  (rationalDualCokernelIsKernel f).conePointUniqueUpToIso
    (limit.isLimit _)

@[reassoc (attr := simp)]
theorem rationalDualCokernelIso_hom_ι {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : C ⟶ D) :
    (rationalDualCokernelIso f).hom ≫ kernel.ι (rationalChainDualMap f) =
      rationalChainDualMap (cokernel.π f) :=
  IsLimit.conePointUniqueUpToIso_hom_comp (rationalDualCokernelIsKernel f)
    (limit.isLimit _) WalkingParallelPair.zero

@[reassoc (attr := simp)]
theorem rationalDualCokernelIso_inv_ι {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : C ⟶ D) :
    (rationalDualCokernelIso f).inv ≫ rationalChainDualMap (cokernel.π f) =
      kernel.ι (rationalChainDualMap f) :=
  IsLimit.conePointUniqueUpToIso_inv_comp (rationalDualCokernelIsKernel f)
    (limit.isLimit _) WalkingParallelPair.zero

/-- The existing relative rational cochain complex is the rational-valued dual
of the existing relative integral chain complex, including differentials. -/
def relativeCochainIntegralDualIso (X : TopCat.{0}) (A : Set X) :
    rationalCochainsForget.obj (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) ≅
      rationalChainDual (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) :=
  PreservesKernel.iso rationalCochainsForget
      (Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A) ≪≫
    kernel.mapIso
      (rationalCochainsForget.map (Cohomology.Singular.RelativeSequence.subspaceCochainRestriction (ModuleCat.of ℚ ℚ) X A))
      (rationalChainDualMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A))
      (rationalSingularCochainDualIso X) (rationalSingularCochainDualIso (TopCat.of A))
      (rationalSingularCochainDualIso_naturality (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X A)) ≪≫
    (rationalDualCokernelIso (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion X A)).symm

/-- The relative duality is exactly the functional induced by the absolute
cochain on the quotient of chains. -/
@[reassoc]
theorem relativeCochainIntegralDualIso_projection (X : TopCat.{0}) (A : Set X) :
    (relativeCochainIntegralDualIso X A).hom ≫
        rationalChainDualMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A) =
      rationalCochainsForget.map (Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A) ≫
        (rationalSingularCochainDualIso X).hom := by
  simp only [relativeCochainIntegralDualIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, rationalDualCokernelIso_inv_ι, kernel.mapIso_hom,
    kernel.lift_ι, PreservesKernel.iso_hom]
  rw [← Category.assoc, kernelComparison_comp_ι]

@[simp]
theorem rationalChainDualMap_comp {C D E : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : C ⟶ D) (g : D ⟶ E) :
    rationalChainDualMap (f ≫ g) = rationalChainDualMap g ≫ rationalChainDualMap f :=
  rationalChainDualFunctor.map_comp g.op f.op

instance rationalDualCokernelProjection_mono {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : C ⟶ D) : Mono (rationalChainDualMap (cokernel.π f)) := by
  rw [← rationalDualCokernelIso_hom_ι f]
  infer_instance

/-- Native pullback of relative cochains is precomposition by the native map
on relative integral chains. -/
@[reassoc]
theorem relativeCochainIntegralDualIso_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) :
    rationalCochainsForget.map (Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f h) ≫
        (relativeCochainIntegralDualIso X A).hom =
      (relativeCochainIntegralDualIso Y B).hom ≫
        rationalChainDualMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap f h) := by
  have hd : rationalChainDualMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap f h) ≫
      rationalChainDualMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A) =
      rationalChainDualMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection Y B) ≫
        rationalChainDualMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f) := by
    rw [← rationalChainDualMap_comp, AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection_naturality,
      rationalChainDualMap_comp]
  apply (cancel_mono (rationalChainDualMap (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A))).1
  rw [Category.assoc, relativeCochainIntegralDualIso_projection,
    ← Category.assoc, ← Functor.map_comp, Cohomology.Singular.RelativeSequence.relativeCochainInclusion_naturality,
    Functor.map_comp, Category.assoc, rationalSingularCochainDualIso_naturality]
  rw [Category.assoc, hd]
  simp only [← Category.assoc, relativeCochainIntegralDualIso_projection]

/-- The degreewise additive form of the actual complex isomorphism. -/
def relativeCochainIntegralDualAddEquiv (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X n ≃+
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X n →ₗ[ℤ] rationalIntegralCoefficient) :=
  (((HomologicalComplex.eval AddCommGrpCat.{0} (ComplexShape.up ℕ) n).mapIso
    (relativeCochainIntegralDualIso X A)).addCommGroupIsoToAddEquiv).trans
      ModuleCat.homAddEquiv

/-- The relative duality also respects the full rational scalar structure. -/
def relativeCochainIntegralDualEquiv (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X n ≃ₗ[ℚ]
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X n →ₗ[ℤ] rationalIntegralCoefficient) where
  __ := relativeCochainIntegralDualAddEquiv X A n
  map_smul' r c := map_rat_smul (relativeCochainIntegralDualAddEquiv X A n) r c

/-- Evaluating on a relative chain represented by an absolute chain agrees
with evaluating the original cochain on that absolute chain. -/
theorem relativeCochainIntegralDualEquiv_projection (X : TopCat.{0}) (A : Set X)
    (n : ℕ) (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X n)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    relativeCochainIntegralDualEquiv X A n c ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f n z) =
      rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) n
        ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f n c) z := by
  have hn := congrArg (fun t => t.f n) (relativeCochainIntegralDualIso_projection X A)
  have he := ConcreteCategory.congr_hom hn
    (show (rationalCochainsForget.obj
      (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A)).X n from c)
  exact congrArg (fun t : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n ⟶ rationalIntegralCoefficient =>
    t z) he

/-- Differential compatibility holds in every pair of degrees, including
the zero maps outside the shape of the complexes. -/
theorem relativeCochainIntegralDualEquiv_d (X : TopCat.{0}) (A : Set X) (i j : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X i)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X j) :
    relativeCochainIntegralDualEquiv X A j
        ((Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).d i j c) z =
      relativeCochainIntegralDualEquiv X A i c ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).d j i z) := by
  have he := ConcreteCategory.congr_hom ((relativeCochainIntegralDualIso X A).hom.comm i j) c
  exact congrArg (fun t : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X j ⟶ rationalIntegralCoefficient =>
    t z) he.symm

/-- Evaluation is natural for genuine continuous maps of pairs. -/
theorem relativeCochainIntegralDualEquiv_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) (n : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) Y B).X n)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X n) :
    relativeCochainIntegralDualEquiv X A n
        ((Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ) f h).f n c) z =
      relativeCochainIntegralDualEquiv Y B n c ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChainsMap f h).f n z) := by
  have hn := congrArg (fun t => t.f n) (relativeCochainIntegralDualIso_naturality f h)
  have he := ConcreteCategory.congr_hom hn
    (show (rationalCochainsForget.obj
      (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) Y B)).X n from c)
  exact congrArg (fun t : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X n ⟶ rationalIntegralCoefficient =>
    t z) he

end

end OAI.AlgebraicTopology.Duality.Poincare.RelativeCochainDual
