import OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldCap
import OAI.AlgebraicGeometry.CycleClass.Geometric.OpenFundamental

/-! # Canonical Cap Naturality -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CanonicalCapNaturality

noncomputable section

/-!
# Open-inclusion naturality of the canonical complex cap map

The canonical compact-support fundamental classes are constructed from the
actual complex orientation. Their proved open-inclusion compatibility gives
the commuting square between extension on compactly supported cohomology,
canonical cap product, and ordinary singular-homology pushforward.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.OpenFundamental.Cycles
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

/-- Actual open inclusion preserves the canonical integral compact-support
class, including its transport to an equal homological degree. -/
theorem complexCompactClassInDegree_open (U : Opens M) (n : ℕ)
    (hn : n = 2 * d) (K : Compacts U) :
    SupportCapNaturality.compactSupportOpenHomologyMap (X := TopCat.of M) U K n
        (ComplexManifoldCap.complexCompactClassInDegree d (M := U) n hn K) =
      ComplexManifoldCap.complexCompactClassInDegree d (M := M) n hn
        (CompactSupportExcision.openSupportImage (X := TopCat.of M) U K) := by
  subst n
  change SupportCapNaturality.compactSupportOpenHomologyMap (X := TopCat.of M) U K (2 * d)
      (AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d (M := U) (K : Set U) K.isCompact) =
    AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles.complexCompactFundamentalClass d (M := M)
      (CompactSupportExcision.openSupportImage (X := TopCat.of M) U K : Set M)
      (CompactSupportExcision.openSupportImage (X := TopCat.of M) U K).isCompact
  exact AlgebraicGeometry.CycleClass.Geometric.OpenFundamental.Cycles.complexCompactFundamentalClass_openInclusion d U (K : Set U) K.isCompact

/-- At each compact support, inverse excision and canonical cap commute
with the genuine ordinary-homology inclusion. -/
@[reassoc]
theorem complexCanonicalRelativeCap_openExtension (U : Opens M)
    (K : Compacts U) (p q : ℕ) (hpq : p + q = 2 * d) :
    (CompactSupportExcision.compactSupportOpenStageIso (X := TopCat.of M) U K p).inv ≫
        SupportCapNaturality.relativeCapWithClass (TopCat.of M)
          (CompactSupportExcision.openSupportImage (X := TopCat.of M) U K : Set M)ᶜ p q
          (ComplexManifoldCap.complexCompactClassInDegree d (M := M) (p + q) hpq
            (CompactSupportExcision.openSupportImage (X := TopCat.of M) U K)) =
      SupportCapNaturality.relativeCapWithClass (TopCat.of U) (K : Set U)ᶜ p q
          (ComplexManifoldCap.complexCompactClassInDegree d (M := U) (p + q) hpq K) ≫
        Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (Opens.inclusion' (X := TopCat.of M) U) q := by
  rw [← complexCompactClassInDegree_open d U (p + q) hpq K]
  exact SupportCapNaturality.relativeCapWithClass_openExtension (X := TopCat.of M) U K p q
    (ComplexManifoldCap.complexCompactClassInDegree d (M := U) (p + q) hpq K)

/-- Canonical cap after open extension equals actual ordinary-homology
inclusion after canonical cap, in every complementary pair of degrees. -/
@[reassoc]
theorem complexManifoldCompactSupportCap_open (U : Opens M)
    (p q : ℕ) (hpq : p + q = 2 * d) :
    CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of M) U p ≫
        ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) p q hpq =
      ComplexManifoldCap.complexManifoldCompactSupportCap d (M := U) p q hpq ≫
        Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (Opens.inclusion' (X := TopCat.of M) U) q :=
  SupportCapNaturality.compactSupportedCapOfCompatibleClasses_open (X := TopCat.of M) U p q
    (ComplexManifoldCap.complexCompactClassInDegree d (M := M) (p + q) hpq)
    (fun _ _ h => ComplexManifoldCap.complexCompactClassInDegree_restriction d (M := M) (p + q) hpq h)
    (ComplexManifoldCap.complexCompactClassInDegree d (M := U) (p + q) hpq)
    (fun _ _ h => ComplexManifoldCap.complexCompactClassInDegree_restriction d (M := U) (p + q) hpq h)
    (fun K => complexCompactClassInDegree_open d U (p + q) hpq K)

/-- Elementwise form of open-inclusion naturality for the canonical cap map. -/
theorem complexManifoldCompactSupportCap_open_apply (U : Opens M)
    (p q : ℕ) (hpq : p + q = 2 * d)
    (c : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) p) :
    ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) p q hpq
        (CompactSupportExcision.compactSupportOpenExtension (X := TopCat.of M) U p c) =
      Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) (Opens.inclusion' (X := TopCat.of M) U) q
        (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := U) p q hpq c) :=
  ConcreteCategory.congr_hom (complexManifoldCompactSupportCap_open d U p q hpq) c

end

end OAI.AlgebraicTopology.Duality.Poincare.CanonicalCapNaturality
