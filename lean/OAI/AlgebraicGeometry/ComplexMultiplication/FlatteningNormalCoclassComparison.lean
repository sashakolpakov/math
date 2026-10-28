import OAI.AlgebraicGeometry.ComplexMultiplication.CenteredFlatteningNormalPair
import OAI.AlgebraicGeometry.ComplexMultiplication.NormalCoclassComparison
import OAI.AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity

/-! # Flattening Normal Coclass Comparison -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.FlatteningNormalCoclassComparison

noncomputable section

/-! # The actual native normal pullback represents the original chart coclass -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Singular

variable {M N E : Type} [TopologicalSpace M] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  (p : ℕ) (f : M → N) (x : M)
  (e : OpenPartialHomeomorph N (E × (Fin p → ℂ)))
  (hx : f x ∈ e.source) (hzero : (e (f x)).2 = 0)
  (hrange : ∀ y ∈ e.source, y ∈ Set.range f ↔ (e y).2 = 0)

local notation "P" => OAI.AlgebraicGeometry.ComplexMultiplication.CenteredFlatteningNormalPair.centeredFlatteningNormalPair f x e hx hzero hrange

/-- The original normal-projection coclass on the actual centered product neighborhood. -/
def originalCenteredNormalPairCoclass :
    AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (P).neighborhood (Set.range f))
      (2 * p) :=
  AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionCoclass E p e (Set.range f) hrange (P).neighborhood (by
    intro y hy
    have hs := (P).neighborhood_subset_source hy
    change y ∈ (CenteredFlatteningNormalPair.centeredFlatteningChart f x e).source at hs
    rwa [CenteredFlatteningNormalPair.centeredFlatteningChart_source] at hs)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [TopologicalSpace M] [NormedSpace ℝ E] in
/-- The comparison retains the genuine normal projection and the fixed nonzero rational scalar. -/
theorem centeredNormalPair_nativeCoclass_comparison :
    RelativeSingularCochainBridge.relativeSingularCohomologyBridgeEquiv ℚ (TopCat.of (P).neighborhood)
      (P).relativeComplement (2 * p)
      ((P).normalCohomologyMap (ModuleCat.of ℚ ℚ) (2 * p)
        (NormalCoclassComparison.normalCoclassCoefficient p • CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)) =
    originalCenteredNormalPairCoclass p f x e hx hzero hrange := by
  rw [ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair.normalCohomologyMap,
    RelativeDualAbsoluteExtension.relativeSingularCohomologyBridgeEquiv_naturality]
  change AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ (2 * p)
    (RelativeDualAbsoluteExtension.originalSubsetPairMap (P).normalCoordinate (P).normalCoordinate_mapsTo)
    (NormalCoclassComparison.normalCohomologyBridge p
      (NormalCoclassComparison.normalCoclassCoefficient p • CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)) = _
  rw [NormalCoclassComparison.normalCoclassCoefficient_smul]
  unfold originalCenteredNormalPairCoclass AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.chartNormalProjectionCoclass
  congr 1
  apply congrArg (AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ (2 * p))
  apply MorphismProperty.Arrow.Hom.ext
  · ext w
    apply Subtype.ext
    change (CenteredFlatteningNormalPair.centeredFlatteningChart f x e w.1.1).2 = (e w.1.1).2
    exact CenteredFlatteningNormalPair.centeredFlatteningChart_normal f x e w.1.1
  · ext w
    change (CenteredFlatteningNormalPair.centeredFlatteningChart f x e w.1).2 = (e w.1).2
    exact CenteredFlatteningNormalPair.centeredFlatteningChart_normal f x e w.1

end

end OAI.AlgebraicGeometry.ComplexMultiplication.FlatteningNormalCoclassComparison
