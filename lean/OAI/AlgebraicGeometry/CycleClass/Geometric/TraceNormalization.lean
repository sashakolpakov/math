import OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace
import OAI.AlgebraicGeometry.CycleClass.Geometric.FundamentalNormalization

/-! # Trace Normalization -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.TraceNormalization

noncomputable section

/-!
# Cap and trace under a change of integral model normalization

The cap maps here descend the actual compatible integral classes through
compact-support cohomology. Scaling the integral family scales its cap and
top-degree trace by the same rational scalar.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.FundamentalNormalization.Cycles
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Duality

/-- Integer scaling of the actual homology argument becomes the same
rational scaling in the ordinary rational cap target. -/
theorem relativeCapHomology_int_smul (X : TopCat.{0}) (A : Set X)
    (p q : ℕ) (k : ℤ)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) X A p)
    (z : LocalHomology.Cycles.relativeSingularHomology X A (p + q)) :
    AlgebraicTopology.Duality.Poincare.SupportRelativeCap.relativeCapHomology X A p q c (k • z) =
      (k : ℚ) • AlgebraicTopology.Duality.Poincare.SupportRelativeCap.relativeCapHomology X A p q c z := by
  rw [Int.cast_smul_eq_zsmul]
  exact map_zsmul (AlgebraicTopology.Duality.Poincare.SupportRelativeCap.relativeCapHomology X A p q c).toAddMonoidHom k z

/-- The actual cap map for a scaled integral class is the corresponding
rational multiple of the original map. -/
theorem relativeCapWithClass_int_smul (X : TopCat.{0}) (A : Set X)
    (p q : ℕ) (k : ℤ) (z : LocalHomology.Cycles.relativeSingularHomology X A (p + q)) :
    AlgebraicTopology.Duality.Poincare.SupportCapNaturality.relativeCapWithClass X A p q (k • z) =
      (k : ℚ) • AlgebraicTopology.Duality.Poincare.SupportCapNaturality.relativeCapWithClass X A p q z := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact relativeCapHomology_int_smul X A p q k c z

/-- Scaling a compatible family of actual integral relative classes scales
its descended compact-support cap map. No existence of a geometric family
is assumed by this general comparison lemma. -/
theorem compactSupportedCapOfCompatibleClasses_eq_int_smul
    (X : TopCat.{0}) (p q : ℕ)
    (z w : ∀ K : Compacts X, LocalHomology.Cycles.relativeSingularHomology X (K : Set X)ᶜ (p + q))
    (hz : ∀ (K L : Compacts X) (h : K ≤ L),
      CompactSupportAssembly.Cycles.homologyWithSupportRestriction X h (p + q) (z L) = z K)
    (hw : ∀ (K L : Compacts X) (h : K ≤ L),
      CompactSupportAssembly.Cycles.homologyWithSupportRestriction X h (p + q) (w L) = w K)
    (k : ℤ) (hscale : ∀ K, w K = k • z K) :
    AlgebraicTopology.Duality.Poincare.SupportCapNaturality.compactSupportedCapOfCompatibleClasses X p q w hw =
      (k : ℚ) • AlgebraicTopology.Duality.Poincare.SupportCapNaturality.compactSupportedCapOfCompatibleClasses X p q z hz := by
  apply AlgebraicTopology.Duality.Poincare.CompactSupportColimit.compactSupportedCohomology_hom_ext (ModuleCat.of ℚ ℚ) X p
  intro K
  rw [AlgebraicTopology.Duality.Poincare.SupportCapNaturality.compactSupportedCapOfCompatibleClasses_stage, Linear.comp_smul,
    AlgebraicTopology.Duality.Poincare.SupportCapNaturality.compactSupportedCapOfCompatibleClasses_stage, hscale K, relativeCapWithClass_int_smul]

variable (d : ℕ) (e : FundamentalNormalization.Cycles.ComplexModelNormalization d)
  {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

/-- The actual compact fundamental class for the supplied integral model
normalization, transported only along an equality of degrees. -/
def complexCompactClassInDegreeWithNormalization (n : ℕ) (hn : n = 2 * d)
    (K : Compacts M) :
    LocalHomology.Cycles.relativeSingularHomology (TopCat.of M) (K : Set M)ᶜ n :=
  (eqToHom (congrArg
    (fun j => LocalHomology.Cycles.relativeSingularHomology (TopCat.of M) (K : Set M)ᶜ j) hn.symm))
      (FundamentalNormalization.Cycles.complexCompactFundamentalClassWithNormalization d e (K : Set M) K.isCompact)

@[simp]
theorem complexCompactClassInDegreeWithNormalization_top (K : Compacts M) :
    complexCompactClassInDegreeWithNormalization d e (2 * d) rfl K =
      FundamentalNormalization.Cycles.complexCompactFundamentalClassWithNormalization d e (K : Set M) K.isCompact := rfl

/-- The reindexed actual classes retain their proved compatibility under
restriction to smaller compact supports. -/
theorem complexCompactClassInDegreeWithNormalization_restriction
    (n : ℕ) (hn : n = 2 * d) {K L : Compacts M} (hKL : K ≤ L) :
    CompactSupportAssembly.Cycles.homologyWithSupportRestriction (TopCat.of M) hKL n
        (complexCompactClassInDegreeWithNormalization d e n hn L) =
      complexCompactClassInDegreeWithNormalization d e n hn K := by
  subst n
  exact FundamentalNormalization.Cycles.complexCompactFundamentalClassWithNormalization_restriction d e
    (K : Set M) (L : Set M) K.isCompact L.isCompact hKL

/-- Comparing actual local normalizations identifies the compact class
with the same integral unit times the canonical compact class. -/
theorem complexCompactClassInDegreeWithNormalization_eq_sign_smul
    (n : ℕ) (hn : n = 2 * d) (K : Compacts M) :
    complexCompactClassInDegreeWithNormalization d e n hn K =
      FundamentalNormalization.Cycles.complexModelNormalizationSign d e • AlgebraicTopology.Duality.Poincare.ComplexManifoldCap.complexCompactClassInDegree d n hn K := by
  subst n
  exact FundamentalNormalization.Cycles.complexCompactFundamentalClassWithNormalization_eq_sign_smul d e
    (K : Set M) K.isCompact

/-- Genuine cap with the compact fundamental classes constructed from
the supplied primitive integral model normalization. The map is defined
by the actual compact-support colimit, not by its scaling comparison. -/
def complexManifoldCompactSupportCapWithNormalization
    (p q : ℕ) (hpq : p + q = 2 * d) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p ⟶
      (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of M)).homology q :=
  AlgebraicTopology.Duality.Poincare.SupportCapNaturality.compactSupportedCapOfCompatibleClasses (TopCat.of M) p q
    (complexCompactClassInDegreeWithNormalization d e (p + q) hpq)
    (fun _ _ h =>
      complexCompactClassInDegreeWithNormalization_restriction d e (p + q) hpq h)

/-- Every compact stage of the normalized cap is exactly cap with that
stage's independently constructed integral fundamental class. -/
@[reassoc (attr := simp)]
theorem complexManifoldCompactSupportCapWithNormalization_stage
    (p q : ℕ) (hpq : p + q = 2 * d) (K : Compacts M) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of M) K p ≫
        complexManifoldCompactSupportCapWithNormalization d e (M := M) p q hpq =
      AlgebraicTopology.Duality.Poincare.SupportCapNaturality.relativeCapWithClass (TopCat.of M) (K : Set M)ᶜ p q
        (complexCompactClassInDegreeWithNormalization d e (p + q) hpq K) :=
  AlgebraicTopology.Duality.Poincare.SupportCapNaturality.compactSupportedCapOfCompatibleClasses_stage (TopCat.of M) p q _ _ K

/-- The compact-stage computation also holds directly on represented
compact-support cohomology classes. -/
@[simp]
theorem complexManifoldCompactSupportCapWithNormalization_stage_apply
    (p q : ℕ) (hpq : p + q = 2 * d) (K : Compacts M)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) (K : Set M)ᶜ p) :
    complexManifoldCompactSupportCapWithNormalization d e (M := M) p q hpq
        (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of M) K p c) =
      AlgebraicTopology.Duality.Poincare.SupportRelativeCap.relativeCapHomology (TopCat.of M) (K : Set M)ᶜ p q c
        (complexCompactClassInDegreeWithNormalization d e (p + q) hpq K) :=
  ConcreteCategory.congr_hom
    (complexManifoldCompactSupportCapWithNormalization_stage d e p q hpq K) c

/-- The actual constructed normalized cap map differs from the canonical
map by the rational image of the integral normalization unit. -/
theorem complexManifoldCompactSupportCapWithNormalization_eq_sign_smul
    (p q : ℕ) (hpq : p + q = 2 * d) :
    complexManifoldCompactSupportCapWithNormalization d e (M := M) p q hpq =
      (FundamentalNormalization.Cycles.complexModelNormalizationSign d e : ℚ) •
        AlgebraicTopology.Duality.Poincare.ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) p q hpq := by
  unfold complexManifoldCompactSupportCapWithNormalization AlgebraicTopology.Duality.Poincare.ComplexManifoldCap.complexManifoldCompactSupportCap
  exact compactSupportedCapOfCompatibleClasses_eq_int_smul (TopCat.of M) p q
    (AlgebraicTopology.Duality.Poincare.ComplexManifoldCap.complexCompactClassInDegree d (p + q) hpq)
    (complexCompactClassInDegreeWithNormalization d e (p + q) hpq)
    (fun _ _ h => AlgebraicTopology.Duality.Poincare.ComplexManifoldCap.complexCompactClassInDegree_restriction d (p + q) hpq h)
    (fun _ _ h =>
      complexCompactClassInDegreeWithNormalization_restriction d e (p + q) hpq h)
    (FundamentalNormalization.Cycles.complexModelNormalizationSign d e)
    (complexCompactClassInDegreeWithNormalization_eq_sign_smul d e (p + q) hpq)

theorem complexManifoldCompactSupportCapWithNormalization_eq_sign_smul_apply
    (p q : ℕ) (hpq : p + q = 2 * d)
    (c : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p) :
    complexManifoldCompactSupportCapWithNormalization d e (M := M) p q hpq c =
      (FundamentalNormalization.Cycles.complexModelNormalizationSign d e : ℚ) •
        AlgebraicTopology.Duality.Poincare.ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) p q hpq c :=
  ConcreteCategory.congr_hom
    (complexManifoldCompactSupportCapWithNormalization_eq_sign_smul d e p q hpq) c

/-- The canonical integral model coordinate recovers the existing
canonical compact-support cap map exactly. -/
@[simp]
theorem complexManifoldCompactSupportCapWithNormalization_canonical
    (p q : ℕ) (hpq : p + q = 2 * d) :
    complexManifoldCompactSupportCapWithNormalization d (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyEquiv d)
        (M := M) p q hpq = AlgebraicTopology.Duality.Poincare.ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) p q hpq := by
  rw [complexManifoldCompactSupportCapWithNormalization_eq_sign_smul,
    FundamentalNormalization.Cycles.complexModelNormalizationSign_canonical, Int.cast_one, one_smul]

/-- The actual top trace for a supplied primitive integral model generator:
cap with its constructed compatible compact classes, followed by augmentation. -/
def complexManifoldTraceWithNormalization :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) (2 * d) ⟶
      ModuleCat.of ℚ ℚ :=
  complexManifoldCompactSupportCapWithNormalization d e (M := M) (2 * d) 0 rfl ≫
    AlgebraicTopology.Duality.Poincare.CapAugmentation.rationalH0Augmentation (TopCat.of M)

@[simp]
theorem complexManifoldTraceWithNormalization_apply
    (c : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) (2 * d)) :
    complexManifoldTraceWithNormalization d e c =
      AlgebraicTopology.Duality.Poincare.CapAugmentation.rationalH0Augmentation (TopCat.of M)
        (complexManifoldCompactSupportCapWithNormalization d e (M := M)
          (2 * d) 0 rfl c) := rfl

/-- On each actual compact support the normalized trace evaluates the
cohomology class on its constructed normalized integral fundamental class. -/
theorem complexManifoldTraceWithNormalization_stage_apply (K : Compacts M)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M)
      (K : Set M)ᶜ (2 * d)) :
    complexManifoldTraceWithNormalization d e
        (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of M) K (2 * d) c) =
      AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of M) (K : Set M)ᶜ (2 * d) c
        (FundamentalNormalization.Cycles.complexCompactFundamentalClassWithNormalization d e (K : Set M) K.isCompact) := by
  rw [complexManifoldTraceWithNormalization_apply,
    complexManifoldCompactSupportCapWithNormalization_stage_apply]
  exact AlgebraicTopology.Duality.Poincare.CapAugmentation.rationalH0Augmentation_relativeCapHomology (TopCat.of M) (K : Set M)ᶜ (2 * d) c
    (FundamentalNormalization.Cycles.complexCompactFundamentalClassWithNormalization d e (K : Set M) K.isCompact)

/-- The same stage formula as an equality of actual rational-linear maps. -/
theorem complexManifoldTraceWithNormalization_stage (K : Compacts M) :
    AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of M) K (2 * d) ≫
        complexManifoldTraceWithNormalization d e =
      ModuleCat.ofHom
        ((LinearMap.applyₗ' ℚ
          (FundamentalNormalization.Cycles.complexCompactFundamentalClassWithNormalization d e (K : Set M) K.isCompact)).comp
          (AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of M) (K : Set M)ᶜ (2 * d))) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact complexManifoldTraceWithNormalization_stage_apply d e K c

/-- On actual cocycle/cycle representatives, normalized trace is exactly
the established relative integral-chain evaluation. -/
theorem complexManifoldTraceWithNormalization_stage_cocycle (K : Compacts M)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of M) (K : Set M)ᶜ) (2 * d))
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (LocalHomology.Cycles.relativeSingularChains (TopCat.of M) (K : Set M)ᶜ) (2 * d))
    (hz : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (LocalHomology.Cycles.relativeSingularChains (TopCat.of M) (K : Set M)ᶜ) (2 * d) z =
      FundamentalNormalization.Cycles.complexCompactFundamentalClassWithNormalization d e (K : Set M) K.isCompact) :
    complexManifoldTraceWithNormalization d e
        (AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of M) K (2 * d)
          (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass
            (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of M) (K : Set M)ᶜ)
            (2 * d) c)) =
      AlgebraicTopology.Duality.Poincare.RelativeCochainDual.relativeCochainIntegralDualEquiv (TopCat.of M) (K : Set M)ᶜ (2 * d) c.val z.val := by
  rw [complexManifoldTraceWithNormalization_stage_apply, ← hz]
  exact AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation_class_class
    (TopCat.of M) (K : Set M)ᶜ (2 * d) c z

/-- Changing the integral model generator multiplies the actual top
trace by the rational image of precisely the same integral unit. -/
theorem complexManifoldTraceWithNormalization_eq_sign_smul :
    complexManifoldTraceWithNormalization d e (M := M) =
      (FundamentalNormalization.Cycles.complexModelNormalizationSign d e : ℚ) • AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := M) := by
  unfold complexManifoldTraceWithNormalization AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace
  rw [complexManifoldCompactSupportCapWithNormalization_eq_sign_smul, Linear.smul_comp]

theorem complexManifoldTraceWithNormalization_eq_sign_mul_apply
    (c : AlgebraicTopology.Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) (2 * d)) :
    complexManifoldTraceWithNormalization d e (M := M) c =
      (FundamentalNormalization.Cycles.complexModelNormalizationSign d e : ℚ) * AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := M) c :=
  ConcreteCategory.congr_hom (complexManifoldTraceWithNormalization_eq_sign_smul d e) c

/-- The canonical model coordinate also recovers the existing trace exactly. -/
@[simp]
theorem complexManifoldTraceWithNormalization_canonical :
    complexManifoldTraceWithNormalization d (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyEquiv d) (M := M) =
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace d (M := M) := by
  rw [complexManifoldTraceWithNormalization_eq_sign_smul,
    FundamentalNormalization.Cycles.complexModelNormalizationSign_canonical, Int.cast_one, one_smul]

end Duality

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.TraceNormalization
