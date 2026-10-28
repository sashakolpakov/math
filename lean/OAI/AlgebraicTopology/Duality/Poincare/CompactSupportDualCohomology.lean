import OAI.AlgebraicTopology.Duality.Poincare.Property
import OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient

/-! # Compact Support Dual Cohomology -/

namespace OAI.AlgebraicTopology.Duality.Poincare

noncomputable section

/-!
Ordinary rational cohomology as the dual of complementary compact-support
cohomology on a genuine complex manifold.

The functional evaluates an ordinary class on the actual canonical cap
product of a compactly supported class. The field universal-coefficient
theorem makes this map an isomorphism under the explicit canonical-cap
duality property. Final geometric
specializations are supplied in CompactSupportDualCohomology. No
finite-dimensionality of either cohomology group is used.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient
open scoped _root_.Manifold

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

/-- The actual pairing: evaluate an ordinary class on the canonical cap
product of a compactly supported class of complementary degree. -/
def CompactSupportDualCohomology.compactSupportEvaluation (p q : ℕ) (hpq : p + q = 2 * d) :
    Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p →ₗ[ℚ]
      Module.Dual ℚ (CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q) :=
  ((ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) q p (by omega)).hom.dualMap).comp
    (Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of M) p)

/-- Evaluation has precisely the ordinary cohomology/homology pairing as
its meaning, with the compact-support class sent by the actual cap map. -/
@[simp]
theorem CompactSupportDualCohomology.compactSupportEvaluation_apply (p q : ℕ) (hpq : p + q = 2 * d)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p)
    (b : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q) :
    CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a b =
      Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of M) p a
        (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) q p (by omega) b) := rfl

/-- On a compact-support stage, the same pairing uses the constructed
integral relative fundamental class of that actual compact subset. -/
theorem CompactSupportDualCohomology.compactSupportEvaluation_stage (p q : ℕ) (hpq : p + q = 2 * d)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p) (K : Compacts M)
    (b : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) (K : Set M)ᶜ q) :
    CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a
        (CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of M) K q b) =
      Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of M) p a
        (SupportRelativeCap.relativeCapHomology (TopCat.of M) (K : Set M)ᶜ q p b
          (ComplexManifoldCap.complexCompactClassInDegree d (q + p) (by omega) K)) := by
  rw [CompactSupportDualCohomology.compactSupportEvaluation_apply, ComplexManifoldCap.complexManifoldCompactSupportCap_stage_apply]

variable (hPD : Property.HasCanonicalPoincareDuality d M)

include hPD

/-- The canonical field UCT followed by the dual of the proved actual cap
isomorphism, using the explicit actual canonical-cap duality property. -/
def Property.HasCanonicalPoincareDuality.compactSupportDualCohomologyEquiv (p q : ℕ) (hpq : p + q = 2 * d) :
    Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p ≃ₗ[ℚ]
      Module.Dual ℚ (CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q) := by
  have hqp : q + p = 2 * d := (Nat.add_comm q p).trans hpq
  let : IsIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) q p hqp) :=
    hPD.cap_isIso q p hqp
  exact (Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := ℚ) (TopCat.of M) p).trans
    ((asIso (ComplexManifoldCap.complexManifoldCompactSupportCap d (M := M) q p hqp)).toLinearEquiv.dualMap)

/-- The canonical equivalence is exactly the actual cap-evaluation map. -/
@[simp]
theorem Property.HasCanonicalPoincareDuality.compactSupportDualCohomologyEquiv_toLinearMap
    (p q : ℕ) (hpq : p + q = 2 * d) :
    (Property.HasCanonicalPoincareDuality.compactSupportDualCohomologyEquiv d hPD (M := M) p q hpq).toLinearMap =
      CompactSupportDualCohomology.compactSupportEvaluation d (M := M) p q hpq := rfl

/-- Pointwise meaning of the canonical duality equivalence. -/
@[simp]
theorem Property.HasCanonicalPoincareDuality.compactSupportDualCohomologyEquiv_apply (p q : ℕ) (hpq : p + q = 2 * d)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p)
    (b : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q) :
    Property.HasCanonicalPoincareDuality.compactSupportDualCohomologyEquiv d hPD p q hpq a b =
      CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a b := rfl

/-- The inverse equivalence realizes every actual functional with exactly
its prescribed evaluations. -/
@[simp]
theorem Property.HasCanonicalPoincareDuality.compactSupportDualCohomologyEquiv_symm_apply
    (p q : ℕ) (hpq : p + q = 2 * d)
    (L : Module.Dual ℚ (CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q))
    (b : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q) :
    CompactSupportDualCohomology.compactSupportEvaluation d p q hpq
        ((Property.HasCanonicalPoincareDuality.compactSupportDualCohomologyEquiv d hPD p q hpq).symm L) b = L b :=
  congrArg (fun f => f b) ((Property.HasCanonicalPoincareDuality.compactSupportDualCohomologyEquiv d hPD p q hpq).apply_symm_apply L)

/-- Every functional on complementary compact-support cohomology is
represented by a unique ordinary rational cohomology class. -/
theorem Property.HasCanonicalPoincareDuality.existsUnique_cohomology_of_compactSupportFunctional
    (p q : ℕ) (hpq : p + q = 2 * d)
    (L : Module.Dual ℚ (CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q)) :
    ∃! a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p,
      ∀ b, CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a b = L b := by
  refine ⟨(Property.HasCanonicalPoincareDuality.compactSupportDualCohomologyEquiv d hPD p q hpq).symm L, ?_, ?_⟩
  · exact Property.HasCanonicalPoincareDuality.compactSupportDualCohomologyEquiv_symm_apply d hPD p q hpq L
  · intro a ha
    apply (Property.HasCanonicalPoincareDuality.compactSupportDualCohomologyEquiv d hPD p q hpq).injective
    apply LinearMap.ext
    intro b
    exact (ha b).trans (Property.HasCanonicalPoincareDuality.compactSupportDualCohomologyEquiv_symm_apply d hPD p q hpq L b).symm

/-- Complementary compact-support tests distinguish ordinary rational
cohomology classes. -/
theorem Property.HasCanonicalPoincareDuality.cohomology_eq_iff_compactSupportEvaluation_eq
    (p q : ℕ) (hpq : p + q = 2 * d)
    (a a' : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p) :
    a = a' ↔ ∀ b, CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a b =
      CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a' b := by
  constructor
  · rintro rfl b
    rfl
  · intro h
    apply (Property.HasCanonicalPoincareDuality.compactSupportDualCohomologyEquiv d hPD p q hpq).injective
    exact LinearMap.ext h

/-- Vanishing against all genuine compact-support tests detects a zero
ordinary cohomology class. -/
theorem Property.HasCanonicalPoincareDuality.cohomology_eq_zero_iff_compactSupportEvaluation_zero
    (p q : ℕ) (hpq : p + q = 2 * d)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p) :
    a = 0 ↔ ∀ b, CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a b = 0 := by
  rw [Property.HasCanonicalPoincareDuality.cohomology_eq_iff_compactSupportEvaluation_eq d hPD p q hpq a 0]
  simp only [map_zero, LinearMap.zero_apply]

/-- A nonzero ordinary class has a complementary compact-support test
with nonzero actual cap evaluation. -/
theorem Property.HasCanonicalPoincareDuality.exists_compactSupport_test_of_ne_zero
    (p q : ℕ) (hpq : p + q = 2 * d)
    {a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p} (ha : a ≠ 0) :
    ∃ b, CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a b ≠ 0 := by
  classical
  apply not_forall.mp
  intro h
  exact ha ((Property.HasCanonicalPoincareDuality.cohomology_eq_zero_iff_compactSupportEvaluation_zero d hPD p q hpq a).mpr h)

/-- Every nonzero compact-support class is detected, with value exactly
one, by an ordinary class. This uses field dual separation, not finite dimension. -/
theorem Property.HasCanonicalPoincareDuality.exists_cohomology_test_eq_one_of_ne_zero
    (p q : ℕ) (hpq : p + q = 2 * d)
    {b : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q} (hb : b ≠ 0) :
    ∃ a, CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a b = 1 := by
  obtain ⟨L, hL⟩ := Module.Projective.exists_dual_eq_one ℚ hb
  refine ⟨(Property.HasCanonicalPoincareDuality.compactSupportDualCohomologyEquiv d hPD p q hpq).symm L, ?_⟩
  rw [Property.HasCanonicalPoincareDuality.compactSupportDualCohomologyEquiv_symm_apply]
  exact hL

/-- Ordinary cohomology tests also detect zero compact-support classes. -/
theorem Property.HasCanonicalPoincareDuality.compactSupport_eq_zero_iff_evaluation_zero
    (p q : ℕ) (hpq : p + q = 2 * d)
    (b : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q) :
    b = 0 ↔ ∀ a, CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a b = 0 := by
  constructor
  · rintro rfl a
    exact map_zero (CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a)
  · intro h
    by_contra hb
    obtain ⟨a, ha⟩ := Property.HasCanonicalPoincareDuality.exists_cohomology_test_eq_one_of_ne_zero d hPD p q hpq hb
    exact one_ne_zero (ha.symm.trans (h a))

/-- The pairing separates compact-support classes as well as ordinary classes. -/
theorem Property.HasCanonicalPoincareDuality.compactSupport_eq_iff_evaluation_eq
    (p q : ℕ) (hpq : p + q = 2 * d)
    (b b' : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q) :
    b = b' ↔ ∀ a, CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a b =
      CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a b' := by
  constructor
  · rintro rfl a
    rfl
  · intro h
    apply sub_eq_zero.mp
    apply (Property.HasCanonicalPoincareDuality.compactSupport_eq_zero_iff_evaluation_zero d hPD p q hpq (b - b')).mpr
    intro a
    rw [map_sub, h a, sub_self]

end

end OAI.AlgebraicTopology.Duality.Poincare
