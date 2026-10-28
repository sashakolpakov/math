import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenProduct
import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.Intersection
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.AnalyticRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SupportLocalDetection

/-! # Closed Intersection Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ClosedIntersectionRestriction.Constructions

noncomputable section

/-! The local diagonal comparison uses exactly the restriction of the
global supported cup and the original finite Serre intersection cycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenProduct.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.Intersection.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Intersection.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectiveSupportIsolation.Constructions.Intersection
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.AnalyticRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.CycleSingleThom.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q)
  (U : Opens (Ambient.Constructions.productVariety V V).analyticSpace)

local notation "D" => OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ComplexImmersion.Constructions.diagonalOpenImmersion V U
local notation "P" => OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction.Constructions.sourceOpen (OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ComplexImmersion.Constructions.diagonalImmersion V) U
local notation "u" => OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenProduct.Constructions.Class.pairedOpenInclusion V p q A B U
local notation "F" => OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V p q A B
abbrev sourceComplement := (ComplexImmersion.Constructions.diagonalOpenImmersion V U).regularComplementInclusion ⁻¹'
  (Set.range (OpenProduct.Constructions.Class.pairedOpenInclusion V p q A B U))ᶜ
local notation "S" => OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ClosedIntersectionRestriction.Constructions.sourceComplement V p q A B U

theorem sourceClosed_complement :
    S = AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeOpenSubspace (X := TopCat.of V.analyticSpace)
      (V.analyticUnderlying ⁻¹' (F : Set V.carrier))ᶜ P := by
  have h := congrArg Set.compl (OpenProduct.Constructions.Class.diagonalOpen_support V p q A B U)
  rw [Closed.Intersection.Constructions.Class.intersectionSupport_eq] at h
  exact h

theorem sourceClosed_mapsTo : Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (P : Set V.analyticSpace))
    S (V.analyticUnderlying ⁻¹' (F : Set V.carrier))ᶜ := by
  intro x hx
  exact (Set.ext_iff.mp (sourceClosed_complement V p q A B U) x).mp hx

theorem sourceClosed_cup :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (P : Set V.analyticSpace))
      (sourceClosed_mapsTo V p q A B U) (2 * (p + q)) (Closed.Intersection.Constructions.Class.closedIntersectionClass V p q A B) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (P : Set V.analyticSpace))
      (OpenProduct.Constructions.Class.sourceCup_mapsTo V p q A B U) (2 * (p + q)) (Supported.Intersection.Constructions.Class.supportedIntersectionClass A B) :=
  Supported.AnalyticRestriction.Constructions.pairMap_targetSupportCast _ (congrArg Set.compl (Closed.Intersection.Constructions.Class.intersectionSupport_eq V p q A B))
    (OpenProduct.Constructions.Class.sourceCup_mapsTo V p q A B U) (sourceClosed_mapsTo V p q A B U) (2 * (p + q)) _

variable (Z : Supported.Map.Constructions.SupportedSupport V (Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V p q A B) (p + q))

theorem sourceComponent_supported :
    (Subtype.val : P → V.analyticSpace) ⁻¹' Set.range Z.val.analyticInclusion ⊆
      (D).regularComplementInclusion ⁻¹' Set.range u := by
  rw [OpenProduct.Constructions.Class.diagonalOpen_support, Closed.Intersection.Constructions.Class.intersectionSupport_eq, Z.val.range_analyticInclusion]
  exact fun _ hz => Z.property hz

variable (hproper : ∀ Z : IrreducibleCloseds V.carrier,
    (Z : Set V.carrier) ⊆ Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V p q A B → p + q ≤ Geometric.DimensionCycles.dimensionCodimension V Z)
  (hother : ∀ W : Supported.Map.Constructions.SupportedSupport V (Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V p q A B) (p + q), W ≠ Z →
    ∀ x : Closed.ImmersionOpenRestriction.Constructions.sourceOpen (ComplexImmersion.Constructions.diagonalImmersion V) U, x.val ∉ Set.range W.val.analyticInclusion)

include hother in
theorem sourceClosed_cycle :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (P : Set V.analyticSpace))
      (sourceClosed_mapsTo V p q A B U) (2 * (p + q))
      (Supported.Map.Constructions.relativeClassMap V F (p + q) (Supported.ProjectiveSupportIsolation.Constructions.Intersection.supportedPairCycle V p q A B hproper)) =
    Open.SupportedLift.Constructions.Map.relativeClassMap V P ((D).regularComplementInclusion ⁻¹' Set.range u) (p + q)
      (Open.SupportedLift.Constructions.restrictCycle V P ((D).regularComplementInclusion ⁻¹' Set.range u) (p + q)
        (Finsupp.single Z.val (IntersectionGeometry.intersectionMultiplicity V.presentation A.val B.val Z.val.val))) := by
  rw [Supported.AnalyticRestriction.Constructions.relativeClassMap_pullback_isolated V F (p + q) P S (sourceClosed_mapsTo V p q A B U)
    (Supported.ProjectiveSupportIsolation.Constructions.Intersection.supportedPairCycle V p q A B hproper) Z hother, Supported.ProjectiveSupportIsolation.Constructions.Intersection.supportedPairCycle_apply,
    Open.CycleSingleThom.Constructions.relativeClassMap_restrict_single V P _ (p + q) Z.val (sourceComponent_supported V p q A B U Z)]
  rfl

include hother in
theorem closedIntersection_restriction_iff :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (V.analyticUnderlying ⁻¹' (F : Set V.carrier))ᶜ P (2 * (p + q)) (Closed.Intersection.Constructions.Class.closedIntersectionClass V p q A B) =
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (V.analyticUnderlying ⁻¹' (F : Set V.carrier))ᶜ P (2 * (p + q))
      (Supported.Map.Constructions.relativeClassMap V F (p + q) (Supported.ProjectiveSupportIsolation.Constructions.Intersection.supportedPairCycle V p q A B hproper)) ↔
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) (P : Set V.analyticSpace))
      (OpenProduct.Constructions.Class.sourceCup_mapsTo V p q A B U) (2 * (p + q)) (Supported.Intersection.Constructions.Class.supportedIntersectionClass A B) =
    Open.SupportedLift.Constructions.Map.relativeClassMap V P ((D).regularComplementInclusion ⁻¹' Set.range u) (p + q)
      (Open.SupportedLift.Constructions.restrictCycle V P ((D).regularComplementInclusion ⁻¹' Set.range u) (p + q)
        (Finsupp.single Z.val (IntersectionGeometry.intersectionMultiplicity V.presentation A.val B.val Z.val.val))) := by
  rw [Scheme.SupportLocalDetection.Constructions.restriction_eq_iff_pairMap _ P S (sourceClosed_complement V p q A B U)
    (sourceClosed_mapsTo V p q A B U), sourceClosed_cup, sourceClosed_cycle V p q A B U Z hproper hother]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.ClosedIntersectionRestriction.Constructions
