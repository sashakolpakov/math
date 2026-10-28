import OAI.AlgebraicTopology.Duality.Poincare.Euclidean
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph
import OAI.AlgebraicTopology.Duality.Poincare.Property
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Euclidean Chart -/

namespace OAI.AlgebraicTopology.Duality.Poincare.EuclideanChart

noncomputable section

/-!
# Poincare duality on a complex manifold homeomorphic to coordinate space

The supplied homeomorphism is used only for the dimensions and vanishing of
the actual (co)homology groups. The canonical complex cap map is shown to be
nonzero by a class supported at one point and dual to the manifold's own
canonical local orientation. No compatibility between the homeomorphism and
the complex charts or orientation is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (d : ℕ) {M : Type} [TopologicalSpace M]

/-- Top compact-support cohomology has rank one under an arbitrary actual
homeomorphism to complex coordinate space. This does not normalize orientation. -/
def euclideanChartTopCohomologyEquiv (e : M ≃ₜ (Fin d → ℂ)) :
    CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) (2 * d) ≃ₗ[ℚ] ℚ :=
  ((CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
    (X := TopCat.of M) (Y := TopCat.of (Fin d → ℂ)) e (2 * d)).symm.toLinearEquiv).trans
      (EuclideanCompactCohomology.complexCompactSupportedTopCohomologyEquiv d)

/-- The non-top compact-support cohomology degrees vanish under the same
purely topological hypothesis. -/
theorem euclideanChartCohomology_isZero (e : M ≃ₜ (Fin d → ℂ))
    (p : ℕ) (hp : p ≠ 2 * d) :
    IsZero (CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p) :=
  (EuclideanCompactCohomology.complexCompactSupportedCohomology_isZero d p hp).of_iso
    (CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
      (X := TopCat.of M) (Y := TopCat.of (Fin d → ℂ)) e p).symm

/-- The actual homeomorphism transports the explicit Euclidean contraction. -/
theorem euclideanChart_contractible (e : M ≃ₜ (Fin d → ℂ)) : ContractibleSpace M := by
  let : ContractibleSpace (Fin d → ℂ) := AlgebraicGeometry.CycleClass.Geometric.ContractibleModel.Cycles.complexNormalModel_contractible d
  exact e.contractibleSpace

/-- Positive rational homology vanishes by that transported contraction. -/
theorem euclideanChartRationalHomology_isZero (e : M ≃ₜ (Fin d → ℂ))
    (q : ℕ) (hq : q ≠ 0) :
    IsZero ((Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of M)).homology q) := by
  let : ContractibleSpace M := euclideanChart_contractible d e
  exact AlgebraicGeometry.CycleClass.Geometric.ContractibleModel.Cycles.isZero_singularHomology_of_contractible (ModuleCat.of ℚ ℚ) (TopCat.of M) q hq

variable [T2Space M] [ChartedSpace (Fin d → ℂ) M]
  [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

/-- The integer local-orientation coefficient at a point, viewed rationally
and precomposed with the actual support-to-point map. -/
def complexSingletonOrientationFunctional (x : M) :
    AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology (TopCat.of M) ({x}ᶜ : Set M) (2 * d) →ₗ[ℤ] ℚ :=
  ((LinearMap.ringLmapEquivSelf ℤ ℚ ℚ).symm 1).comp
    (((AlgebraicGeometry.CycleClass.Geometric.ComplexChartOrientation.Cycles.complexChartTopLocalIso (chartAt (Fin d → ℂ) x) x
      (mem_chart_source (Fin d → ℂ) x)).toLinearEquiv.toLinearMap).comp
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) {x} x (Set.mem_singleton x) (2 * d)).hom)

/-- This functional evaluates the actual singleton compact fundamental class
to one in the canonical complex orientation. -/
theorem complexSingletonOrientationFunctional_class (x : M) :
    complexSingletonOrientationFunctional d x
        (AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d ({x} : Set M) isCompact_singleton) = 1 := by
  change ((LinearMap.ringLmapEquivSelf ℤ ℚ ℚ).symm 1)
    ((AlgebraicGeometry.CycleClass.Geometric.ComplexChartOrientation.Cycles.complexChartTopLocalIso (chartAt (Fin d → ℂ) x) x
      (mem_chart_source (Fin d → ℂ) x)).toLinearEquiv
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) {x} x (Set.mem_singleton x) (2 * d)
        (AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d ({x} : Set M) isCompact_singleton))) = 1
  rw [AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass_atPoint]
  have hn : (AlgebraicGeometry.CycleClass.Geometric.ComplexChartOrientation.Cycles.complexChartTopLocalIso (chartAt (Fin d → ℂ) x) x
      (mem_chart_source (Fin d → ℂ) x)).toLinearEquiv
      (AlgebraicGeometry.CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x) = 1 :=
    AlgebraicGeometry.CycleClass.Geometric.ComplexChartOrientation.Cycles.complexChartLocalClass_normalization (chartAt (Fin d → ℂ) x) x
      (mem_chart_source (Fin d → ℂ) x)
  rw [hn]
  simp

/-- Every point supplies an actual compact-support top cohomology class
whose cap product has augmentation one. This construction uses the manifold's
own local generator and does not involve any external homeomorphism. -/
theorem exists_complexTopCap_augmentation_one (x : M) :
    ∃ c : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) (2 * d),
      CapAugmentation.rationalH0Augmentation (TopCat.of M)
        (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) (2 * d) 0 rfl c) = 1 := by
  let K : Compacts M := ⟨{x}, isCompact_singleton⟩
  let c := (RelativeUniversalCoefficient.relativeRationalUniversalCoefficientEquiv (TopCat.of M)
    (K : Set M)ᶜ (2 * d)).symm (complexSingletonOrientationFunctional d x)
  refine ⟨CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of M) K (2 * d) c, ?_⟩
  calc
    _ = CapAugmentation.rationalH0Augmentation (TopCat.of M)
        (SupportRelativeCap.relativeCapHomology (TopCat.of M) (K : Set M)ᶜ (2 * d) 0 c
          (ComplexManifoldCap.complexCompactClassInDegree d (2 * d + 0) rfl K)) :=
      congrArg (CapAugmentation.rationalH0Augmentation (TopCat.of M))
        (ComplexManifoldCap.complexManifoldCompactSupportCap_stage_apply d (2 * d) 0 rfl K c)
    _ = RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of M) (K : Set M)ᶜ (2 * d) c
        (AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d ({x} : Set M) isCompact_singleton) :=
      CapAugmentation.rationalH0Augmentation_relativeCapHomology (TopCat.of M) (K : Set M)ᶜ
        (2 * d) c (ComplexManifoldCap.complexCompactClassInDegree d (2 * d + 0) rfl K)
    _ = complexSingletonOrientationFunctional d x
        (AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d ({x} : Set M) isCompact_singleton) := by
      change (RelativeUniversalCoefficient.relativeRationalUniversalCoefficientEquiv (TopCat.of M)
        (K : Set M)ᶜ (2 * d) c) _ = _
      rw [LinearEquiv.apply_symm_apply]
      rfl
    _ = 1 := complexSingletonOrientationFunctional_class d x

private theorem scalarComparison_isIso_of_surjective
    {V : ModuleCat.{0} ℚ} (e : V ≃ₗ[ℚ] ℚ) (f : V ⟶ ModuleCat.of ℚ ℚ)
    (hf : Function.Surjective f) : IsIso f := by
  let g : ℚ →ₗ[ℚ] ℚ := f.hom.comp e.symm.toLinearMap
  have hg : Function.Surjective g := hf.comp e.symm.surjective
  have hg' : Function.Injective g := (LinearMap.injective_iff_surjective).mpr hg
  have hfi : Function.Injective f := by
    intro a b hab
    apply e.injective
    apply hg'
    simpa only [g, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] using hab
  exact (LinearEquiv.ofBijective f.hom ⟨hfi, hf⟩).toModuleIso.isIso_hom

/-- The top canonical cap map is an isomorphism when the underlying space is
homeomorphic to coordinate space. The homeomorphism need not preserve the
complex structure or its orientation. -/
theorem euclideanChartCap_top_isIso (e : M ≃ₜ (Fin d → ℂ)) :
    IsIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) (2 * d) 0 rfl) := by
  let : PathConnectedSpace M := e.symm.surjective.pathConnectedSpace e.symm.continuous
  let f := ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) (2 * d) 0 rfl ≫
    CapAugmentation.rationalH0Augmentation (TopCat.of M)
  have hf : Function.Surjective f := by
    obtain ⟨c, hc⟩ := exists_complexTopCap_augmentation_one d (e.symm 0)
    intro a
    refine ⟨a • c, ?_⟩
    rw [map_smul]
    change a • CapAugmentation.rationalH0Augmentation (TopCat.of M)
      (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) (2 * d) 0 rfl c) = a
    rw [hc]
    simp
  let : IsIso f := scalarComparison_isIso_of_surjective
    (euclideanChartTopCohomologyEquiv d e) f hf
  let : IsIso (CapAugmentation.rationalH0Augmentation (TopCat.of M)) := by
    change IsIso ((TopCat.of M).singularHomology₀ε
      (C := ModuleCat.{0} ℚ) (ModuleCat.of ℚ ℚ))
    infer_instance
  exact IsIso.of_isIso_comp_right
    (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) (2 * d) 0 rfl)
    (CapAugmentation.rationalH0Augmentation (TopCat.of M))

/-- Actual local Poincare duality under a purely topological Euclidean-chart
hypothesis, in every complementary pair of nonnegative degrees. -/
theorem euclideanChartPoincareDuality_isIso (e : M ≃ₜ (Fin d → ℂ))
    (p q : ℕ) (hpq : p + q = 2 * d) :
    IsIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) p q hpq) := by
  by_cases hq : q = 0
  · subst q
    have hp : p = 2 * d := by simpa only [Nat.add_zero] using hpq
    subst p
    exact euclideanChartCap_top_isIso d e
  · exact (euclideanChartCohomology_isZero d e p (by omega)).isIso
      (euclideanChartRationalHomology_isZero d e q hq) _

/-- The isomorphism packages the manifold's actual canonical cap map. -/
def euclideanChartPoincareDuality (e : M ≃ₜ (Fin d → ℂ))
    (p q : ℕ) (hpq : p + q = 2 * d) :
    CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p ≅
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of M)).homology q := by
  let : IsIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) p q hpq) :=
    euclideanChartPoincareDuality_isIso d e p q hpq
  exact asIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) p q hpq)

@[simp]
theorem euclideanChartPoincareDuality_hom (e : M ≃ₜ (Fin d → ℂ))
    (p q : ℕ) (hpq : p + q = 2 * d) :
    (euclideanChartPoincareDuality d e p q hpq).hom =
      ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) p q hpq := rfl

/-- The full local induction property follows from the actual cap
isomorphisms and the separately proved higher cohomology vanishing. -/
theorem euclideanChart_hasCanonicalPoincareDuality (e : M ≃ₜ (Fin d → ℂ)) :
    Property.HasCanonicalPoincareDuality d M :=
  ⟨fun p q hpq => euclideanChartPoincareDuality_isIso d e p q hpq,
    fun p hp => euclideanChartCohomology_isZero d e p (by omega)⟩

end

end OAI.AlgebraicTopology.Duality.Poincare.EuclideanChart
