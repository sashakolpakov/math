import OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldCap
import OAI.AlgebraicTopology.Duality.Poincare.EuclideanCompactCohomology
import OAI.AlgebraicTopology.Cohomology.Singular.CubicalTriangulationComparison
import OAI.AlgebraicTopology.Products.Cup

/-! # Cap Augmentation -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CapAugmentation

noncomputable section

/-!
# Augmentation of the actual relative cap product

In output degree zero, augmenting the cap product is exactly evaluation of
the cochain on the original chain. We prove this first for actual singular
simplices, then for finite chains, the relative quotient, and the existing
categorical (co)homology groups.

For complex coordinate space this identifies the canonical manifold cap map
followed by the actual zeroth-homology augmentation with the already proved
normalized compact-support cohomology equivalence.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.CubicalTriangulationComparison OAI.AlgebraicTopology.Products.Cup
open scoped Simplicial _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The canonical rational singular-homology augmentation already defined
by mathlib, sending every point class to one. -/
abbrev rationalH0Augmentation (X : TopCat.{0}) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology 0 ⟶ ModuleCat.of ℚ ℚ :=
  X.singularHomology₀ε (C := ModuleCat.{0} ℚ) (ModuleCat.of ℚ ℚ)

/-- The same canonical augmentation on actual rational zero-chains. Every
zero-chain is a cycle in the existing nonnegative chain complex. -/
def rationalZeroChainAugmentation (X : TopCat.{0}) :
    (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X 0 →ₗ[ℚ] ℚ :=
  (rationalH0Augmentation X).hom.comp
    ((Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) 0).comp
      ((LinearMap.id).codRestrict (Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) 0)
        (fun z => Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) z)))

@[simp]
theorem rationalZeroChainAugmentation_apply (X : TopCat.{0})
    (z : (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X 0) :
    rationalZeroChainAugmentation X z =
      rationalH0Augmentation X
        (Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) 0
          ⟨z, Cohomology.Singular.ChainRepresentatives.mem_chainCycles_zero (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) z⟩) := rfl

/-- Each genuine zero-simplex contributes exactly its coefficient. -/
@[simp]
theorem rationalZeroChainAugmentation_simplex (X : TopCat.{0})
    (s : (TopCat.toSSet.obj X) _⦋0⦌) :
    rationalZeroChainAugmentation X (Cohomology.Singular.ChainDual.simplexChain (R := ℚ) (TopCat.toSSet.obj X) s) = 1 :=
  Cohomology.Singular.CubicalTriangulationComparison.chainClass_simplex_homologyZeroAugmentation (TopCat.toSSet.obj X)
    (ModuleCat.of ℚ ℚ) s 1

/-- Augmenting a mixed cap with output degree zero evaluates the original
rational cochain on the original finite integral chain. -/
theorem rationalZeroChainAugmentation_mixedCap (X : TopCat.{0}) (p : ℕ)
    (c : (Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X p) :
    rationalZeroChainAugmentation X (IntegralCapCoefficients.mixedSingularCap X p 0 c z) =
      RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) p c z := by
  have h : ((rationalZeroChainAugmentation X).restrictScalars ℤ).comp
      (IntegralCapCoefficients.mixedSingularCap X p 0 c) =
      RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) p c := by
    apply Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj X) RelativeCochainDual.rationalIntegralCoefficient
    intro s
    change rationalZeroChainAugmentation X
        (IntegralCapCoefficients.mixedSimplicialCap (TopCat.toSSet.obj X) p 0 c
          (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) s)) =
      RelativeCochainDual.rationalSimplicialChainDualEquiv (TopCat.toSSet.obj X) p c
        (Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) s)
    rw [IntegralCapCoefficients.mixedSimplicialCap_simplex, map_smul, rationalZeroChainAugmentation_simplex,
      smul_eq_mul, mul_one, RelativeCochainDual.rationalSimplicialChainDualEquiv_simplex, Products.Cup.frontFace_zero_right]
  exact LinearMap.congr_fun h z

/-- The coefficient-sum formula descends through the actual relative
chain quotient and agrees with its already constructed cochain duality. -/
theorem rationalZeroChainAugmentation_relativeCap (X : TopCat.{0}) (A : Set X) (p : ℕ)
    (c : (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A).X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A).X p) :
    rationalZeroChainAugmentation X (SupportRelativeCap.relativeCap X A p 0 c z) =
      RelativeCochainDual.relativeCochainIntegralDualEquiv X A p c z := by
  obtain ⟨z, rfl⟩ := SupportRelativeCap.relativeChainProjection_surjective X A p z
  have hcap : SupportRelativeCap.relativeCap X A p 0 c ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X A).f p z) =
      IntegralCapCoefficients.mixedSingularCap X p 0 ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c) z := by
    simpa only [Nat.add_zero] using SupportRelativeCap.relativeCap_projection X A p 0 c z
  exact (congrArg (rationalZeroChainAugmentation X) hcap).trans
    ((rationalZeroChainAugmentation_mixedCap X p
      ((Cohomology.Singular.RelativeSequence.relativeCochainInclusion (ModuleCat.of ℚ ℚ) X A).f p c) z).trans
        (RelativeCochainDual.relativeCochainIntegralDualEquiv_projection X A p c z).symm)

/-- On genuine relative (co)homology, augmenting the cap class is exactly
the canonical evaluation pairing with the integral relative class. -/
theorem rationalH0Augmentation_relativeCapHomology (X : TopCat.{0}) (A : Set X) (p : ℕ)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A p) :
    rationalH0Augmentation X (SupportRelativeCap.relativeCapHomology X A p 0 c z) =
      RelativeUniversalCoefficient.relativeRationalHomologyEvaluation X A p c z := by
  obtain ⟨c, rfl⟩ := Cohomology.Singular.Representatives.cochainClass_surjective
    (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p c
  obtain ⟨z, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) p z
  have hcap : SupportRelativeCap.relativeCapHomology X A p 0
      (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) X A) p c)
      (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains X A) p z) =
      Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) 0 (SupportRelativeCap.relativeCapCycles X A p 0 c z) := by
    simpa only [Nat.add_zero] using SupportRelativeCap.relativeCapHomology_class_class X A p 0 c z
  have heval : rationalH0Augmentation X
      (Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) 0 (SupportRelativeCap.relativeCapCycles X A p 0 c z)) =
      RelativeCochainDual.relativeCochainIntegralDualEquiv X A p c.val z.val := by
    change rationalZeroChainAugmentation X (SupportRelativeCap.relativeCap X A p 0 c.val z.val) = _
    exact rationalZeroChainAugmentation_relativeCap X A p c.val z.val
  exact (congrArg (rationalH0Augmentation X) hcap).trans
    (heval.trans (RelativeUniversalCoefficient.relativeRationalHomologyEvaluation_class_class X A p c z).symm)

/-- The augmentation identity as an equality of actual rational-linear maps. -/
@[reassoc]
theorem relativeCapWithClass_augmentation (X : TopCat.{0}) (A : Set X) (p : ℕ)
    (z : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology X A p) :
    SupportCapNaturality.relativeCapWithClass X A p 0 z ≫ rationalH0Augmentation X =
      ModuleCat.ofHom ((LinearMap.applyₗ' ℚ z).comp
        (RelativeUniversalCoefficient.relativeRationalHomologyEvaluation X A p)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact rationalH0Augmentation_relativeCapHomology X A p c z

set_option backward.isDefEq.respectTransparency.types true

/-- At each compact support, the actual canonical cap has the exact
coordinate normalization, via the proved equality of fundamental classes. -/
theorem complexManifoldCompactSupportCap_augmentation_stage (d : ℕ)
    (K : Compacts (Fin d → ℂ))
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ))
      (K : Set (Fin d → ℂ))ᶜ (2 * d)) :
    rationalH0Augmentation (TopCat.of (Fin d → ℂ))
        (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := Fin d → ℂ) (2 * d) 0 rfl
          (CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) K (2 * d) c)) =
      EuclideanCompactCohomology.complexCompactSupportedTopCohomologyEquiv d
        (CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) K (2 * d) c) := by
  have hcap := congrArg (rationalH0Augmentation (TopCat.of (Fin d → ℂ)))
    (ComplexManifoldCap.complexManifoldCompactSupportCap_stage_apply d (2 * d) 0 rfl K c)
  have heval := rationalH0Augmentation_relativeCapHomology (TopCat.of (Fin d → ℂ))
    (K : Set (Fin d → ℂ))ᶜ (2 * d) c
    (ComplexManifoldCap.complexCompactClassInDegree d (2 * d + 0) rfl K)
  have hclass : ComplexManifoldCap.complexCompactClassInDegree d (2 * d + 0) rfl K =
      AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.complexCompactSupportClass d K K.isCompact :=
    ComplexManifoldCap.complexCompactFundamentalClass_eq_coordinate d K K.isCompact
  exact hcap.trans (heval.trans ((congrArg
    (RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of (Fin d → ℂ))
      (K : Set (Fin d → ℂ))ᶜ (2 * d) c) hclass).trans
        (EuclideanCompactCohomology.complexCompactSupportedTopCohomologyEquiv_stage d K c).symm))

/-- Elementwise form of the exact Euclidean cap normalization, obtained
from a genuine compact support representing the given class. -/
theorem complexManifoldCompactSupportCap_augmentation_apply (d : ℕ)
    (c : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of (Fin d → ℂ)) (2 * d)) :
    rationalH0Augmentation (TopCat.of (Fin d → ℂ))
        (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := Fin d → ℂ) (2 * d) 0 rfl c) =
      EuclideanCompactCohomology.complexCompactSupportedTopCohomologyEquiv d c := by
  obtain ⟨K, a, rfl⟩ := CompactSupportColimit.compactSupportedCohomology_exists_stage (ModuleCat.of ℚ ℚ)
    (TopCat.of (Fin d → ℂ)) (2 * d) c
  exact complexManifoldCompactSupportCap_augmentation_stage d K a

/-- The actual canonical cap map on complex coordinate space has the exact
normalization of its compact-support cohomology equivalence. This includes
complex dimension zero. -/
@[reassoc]
theorem complexManifoldCompactSupportCap_augmentation (d : ℕ) :
    ComplexManifoldCap.complexManifoldCompactSupportCap d (M := Fin d → ℂ) (2 * d) 0 rfl ≫
        rationalH0Augmentation (TopCat.of (Fin d → ℂ)) =
      ModuleCat.ofHom (EuclideanCompactCohomology.complexCompactSupportedTopCohomologyEquiv d).toLinearMap := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact complexManifoldCompactSupportCap_augmentation_apply d c

end

end OAI.AlgebraicTopology.Duality.Poincare.CapAugmentation
