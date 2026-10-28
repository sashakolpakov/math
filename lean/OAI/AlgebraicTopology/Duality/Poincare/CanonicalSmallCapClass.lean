import OAI.AlgebraicTopology.Duality.Poincare.SmallSupportedCapClass
import OAI.AlgebraicTopology.Duality.Poincare.CanonicalCapExcisionClass
import OAI.AlgebraicTopology.Duality.Poincare.CapMayerVietorisColimit

/-! # Canonical Small Cap Class -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CanonicalSmallCapClass

noncomputable section

/-!
# Canonical compact-stage cap classes represented by small chains

A genuine small relative cycle representing the canonical compact fundamental
class gives exactly the existing compact-stage cap map of an open submanifold.
The equality takes place in that submanifold's own rational homology.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

/-- A small relative representative of the actual canonical compact class
computes the actual open-stage canonical cap map, inside the open set. -/
theorem smallSupportedRelativeCapCycle_class_eq_openStageCap
    (W : Opens M) (K : W.compactsInside) (p q : ℕ) (hpq : p + q = 2 * d)
    (a : Cohomology.Singular.Representatives.cochainCocycles (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
      (TopCat.of M) (K.val : Set M)ᶜ) p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.SmallMayerVietoris.Cycles.binarySmallSingularChains (TopCat.of M) (W : Set M) (K.val : Set M)ᶜ).X
      (p + q))
    (hz : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) (K.val : Set M)ᶜ).f (p + q)
      ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion (TopCat.of M) (W : Set M)
        (K.val : Set M)ᶜ).f (p + q) z) ∈
      Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of M) (K.val : Set M)ᶜ) (p + q))
    (hclass : Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularChains (TopCat.of M) (K.val : Set M)ᶜ)
      (p + q)
      ⟨(AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of M) (K.val : Set M)ᶜ).f (p + q)
        ((AlgebraicGeometry.CycleClass.Geometric.BinarySmallInclusion.Cycles.binarySmallIntegralChainInclusion (TopCat.of M) (W : Set M)
          (K.val : Set M)ᶜ).f (p + q) z), hz⟩ =
      ComplexManifoldCap.complexCompactClassInDegree d (M := M) (p + q) hpq K.val) :
    Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of W)) q
      (SmallSupportedCapClass.smallSupportedRelativeCapCycle (TopCat.of M) (W : Set M)
        (K.val : Set M)ᶜ p q a z hz) =
    CapMayerVietorisColimit.complexManifoldOpenStageCap d W K p q hpq
      (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
        (TopCat.of M) (K.val : Set M)ᶜ) p a) := by
  have hlocal := SmallSupportedCapClass.smallSupportedRelativeCapCycle_class_excision (TopCat.of M)
    (W : Set M) (K.val : Set M) K.val.isCompact W.isOpen K.property p q a z hz
  have hfundamental := (congrArg
    (AlgebraicGeometry.CycleClass.Geometric.CompactSupportExcision.Cycles.compactSupportExcisionHomologyIso (TopCat.of M) (W : Set M) (K.val : Set M)
      K.val.isCompact W.isOpen K.property (p + q)).inv hclass).trans
      (CanonicalCapExcisionClass.complexCompactClassInDegree_openExcision_preimage d W K (p + q) hpq)
  exact hlocal.trans (congrArg
    (SupportRelativeCap.relativeCapHomology (TopCat.of W)
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (W : Set M)) ⁻¹' (K.val : Set M)ᶜ) p q
      ((HomologicalComplex.homologyMap
        (CompactSupportExcision.compactSupportExcisionCochainMap (TopCat.of M) (W : Set M) (K.val : Set M)) p)
        (Cohomology.Singular.Representatives.cochainClass (Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
          (TopCat.of M) (K.val : Set M)ᶜ) p a))) hfundamental)

end

end OAI.AlgebraicTopology.Duality.Poincare.CanonicalSmallCapClass
