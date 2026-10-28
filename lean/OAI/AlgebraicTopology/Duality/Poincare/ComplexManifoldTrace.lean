import OAI.AlgebraicTopology.Duality.Poincare.CapAugmentation
import OAI.AlgebraicTopology.Duality.Poincare.CanonicalCapNaturality
import OAI.AlgebraicTopology.Duality.Poincare.NestedOpenCapNaturality

/-! # Complex Manifold Trace -/

namespace OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace

noncomputable section

/-!
# The actual top-degree trace on a complex manifold

The trace on compactly supported rational cohomology is the canonical cap
map followed by the ordinary zeroth-homology augmentation. At each compact
support it evaluates on the constructed integral fundamental class. Actual
open extension preserves the trace. No cap-isomorphism hypothesis is used.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Continuous pushforward preserves the coefficient sum on genuine
rational zero-chains. -/
theorem rationalZeroChainAugmentation_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (CapAugmentation.rationalZeroChainAugmentation Y).comp ((Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) f).f 0).hom =
      CapAugmentation.rationalZeroChainAugmentation X := by
  apply Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ)
  intro s
  change CapAugmentation.rationalZeroChainAugmentation Y
      ((Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap (R := ℚ) (TopCat.toSSet.map f)).f 0
        (Cohomology.Singular.ChainDual.simplexChain (R := ℚ) (TopCat.toSSet.obj X) s)) =
    CapAugmentation.rationalZeroChainAugmentation X (Cohomology.Singular.ChainDual.simplexChain (R := ℚ) (TopCat.toSSet.obj X) s)
  rw [Cohomology.Singular.EvaluationNaturality.simplicialScalarChainMap_simplex, CapAugmentation.rationalZeroChainAugmentation_simplex,
    CapAugmentation.rationalZeroChainAugmentation_simplex]

/-- The actual rational zeroth-homology augmentation is natural under
every continuous map, without a connectedness assumption. -/
theorem rationalH0Augmentation_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f 0 ≫ CapAugmentation.rationalH0Augmentation Y =
      CapAugmentation.rationalH0Augmentation X := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨c, rfl⟩ := Cohomology.Singular.ChainRepresentatives.chainClass_surjective (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) 0 z
  change CapAugmentation.rationalH0Augmentation Y
      (Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f 0
        (Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) 0 c)) =
    CapAugmentation.rationalH0Augmentation X (Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) 0 c)
  rw [Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward_class]
  change CapAugmentation.rationalZeroChainAugmentation Y ((Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) f).f 0 c.val) =
    CapAugmentation.rationalZeroChainAugmentation X c.val
  exact LinearMap.congr_fun (rationalZeroChainAugmentation_naturality f) c.val

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

/-- The canonical trace is actual cap with the constructed complex
orientation followed by the genuine rational H₀ augmentation. -/
def complexManifoldTrace :
    CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) (2 * d) ⟶
      ModuleCat.of ℚ ℚ :=
  ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) (2 * d) 0 rfl ≫
    CapAugmentation.rationalH0Augmentation (TopCat.of M)

@[simp]
theorem complexManifoldTrace_apply
    (c : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) (2 * d)) :
    complexManifoldTrace d c = CapAugmentation.rationalH0Augmentation (TopCat.of M)
      (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) (2 * d) 0 rfl c) :=
  rfl

/-- At a compact support, trace is evaluation on the actual integral
fundamental class with that support. -/
theorem complexManifoldTrace_stage_apply (K : Compacts M)
    (c : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) (K : Set M)ᶜ (2 * d)) :
    complexManifoldTrace d
        (CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of M) K (2 * d) c) =
      RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of M) (K : Set M)ᶜ (2 * d) c
        (AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d (K : Set M) K.isCompact) := by
  rw [complexManifoldTrace_apply, ComplexManifoldCap.complexManifoldCompactSupportCap_stage_apply]
  exact CapAugmentation.rationalH0Augmentation_relativeCapHomology (TopCat.of M) (K : Set M)ᶜ
    (2 * d) c (AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d (K : Set M) K.isCompact)

/-- The compact-stage formula as an equality of actual rational-linear maps. -/
theorem complexManifoldTrace_stage (K : Compacts M) :
    CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of M) K (2 * d) ≫
        complexManifoldTrace d =
      ModuleCat.ofHom
        ((LinearMap.applyₗ' ℚ (AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d (K : Set M) K.isCompact)).comp
          (RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of M) (K : Set M)ᶜ (2 * d))) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact complexManifoldTrace_stage_apply d K c

/-- On actual representatives, trace is the genuine relative cochain
evaluated on a cycle representing the constructed fundamental class. -/
theorem complexManifoldTrace_stage_cocycle (K : Compacts M)
    (c : Cohomology.Singular.Representatives.cochainCocycles
      (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of M) (K : Set M)ᶜ) (2 * d))
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of M) (K : Set M)ᶜ) (2 * d))
    (hz : Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of M) (K : Set M)ᶜ) (2 * d) z =
      AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d (K : Set M) K.isCompact) :
    complexManifoldTrace d
        (CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of M) K (2 * d)
          (Cohomology.Singular.Representatives.cochainClass
            (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of M) (K : Set M)ᶜ)
            (2 * d) c)) =
      RelativeCochainDual.relativeCochainIntegralDualEquiv (TopCat.of M) (K : Set M)ᶜ (2 * d) c.val z.val := by
  rw [complexManifoldTrace_stage_apply, ← hz]
  exact RelativeUniversalCoefficient.relativeRationalHomologyEvaluation_class_class
    (TopCat.of M) (K : Set M)ᶜ (2 * d) c z

/-- Extending a compactly supported class from an open submanifold
preserves its actual top trace. -/
theorem complexManifoldTrace_open (U : Opens M) :
    CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of M) U (2 * d) ≫
        complexManifoldTrace d (M := M) =
      complexManifoldTrace d (M := U) := by
  unfold complexManifoldTrace
  rw [← Category.assoc, CanonicalCapNaturality.complexManifoldCompactSupportCap_open, Category.assoc,
    rationalH0Augmentation_naturality]
  rfl

theorem complexManifoldTrace_open_apply (U : Opens M)
    (c : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) (2 * d)) :
    complexManifoldTrace d (M := M)
        (CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of M) U (2 * d) c) =
      complexManifoldTrace d (M := U) c :=
  ConcreteCategory.congr_hom (complexManifoldTrace_open d U) c

/-- The same compatibility holds for extension between any nested opens. -/
theorem complexManifoldTrace_opensInclusion (U V : Opens M) (h : U ≤ V) :
    CompactSupportOpen.compactSupportOpenMap (X := TopCat.of M) h (2 * d) ≫
        complexManifoldTrace d (M := V) =
      complexManifoldTrace d (M := U) := by
  unfold complexManifoldTrace
  rw [← Category.assoc, NestedOpenCapNaturality.complexManifoldCompactSupportCap_opensInclusion, Category.assoc,
    rationalH0Augmentation_naturality]

theorem complexManifoldTrace_opensInclusion_apply (U V : Opens M) (h : U ≤ V)
    (c : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) (2 * d)) :
    complexManifoldTrace d (M := V)
        (CompactSupportOpen.compactSupportOpenMap (X := TopCat.of M) h (2 * d) c) =
      complexManifoldTrace d (M := U) c :=
  ConcreteCategory.congr_hom (complexManifoldTrace_opensInclusion d U V h) c

/-- On complex coordinate space, this trace is exactly the established
normalized compact-support cohomology map, including dimension zero. -/
theorem complexManifoldTrace_coordinate :
    complexManifoldTrace d (M := Fin d → ℂ) =
      ModuleCat.ofHom (EuclideanCompactCohomology.complexCompactSupportedTopCohomologyEquiv d).toLinearMap :=
  CapAugmentation.complexManifoldCompactSupportCap_augmentation d

end

end OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace
