import OAI.AlgebraicTopology.Duality.Poincare.Manifold
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportDualCohomology

/-! # Compact Support And -/

namespace OAI.AlgebraicTopology.Duality.Poincare.CompactSupportAnd

noncomputable section

/-!
Ordinary rational cohomology as the dual of complementary compact-support
cohomology on a genuine complex manifold.

The functional evaluates an ordinary class on the actual canonical cap
product of a compactly supported class. The field universal-coefficient
theorem and the proved canonical Poincare duality theorem make this map an
isomorphism. No finite-dimensionality of either cohomology group is used.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

section SecondCountable

variable [SecondCountableTopology M]

/-- The canonical field UCT followed by the dual of the proved actual cap
isomorphism. All geometric duality premises are discharged by the manifold
Poincare duality theorem. -/
def compactSupportDualCohomologyEquiv (p q : ℕ) (hpq : p + q = 2 * d) :
    Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p ≃ₗ[ℚ]
      Module.Dual ℚ (CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q) :=
  Property.HasCanonicalPoincareDuality.compactSupportDualCohomologyEquiv d
    (Manifold.complexManifold_hasCanonicalPoincareDuality d (M := M)) p q hpq

/-- The canonical equivalence is exactly the actual cap-evaluation map. -/
@[simp]
theorem compactSupportDualCohomologyEquiv_toLinearMap
    (p q : ℕ) (hpq : p + q = 2 * d) :
    (compactSupportDualCohomologyEquiv d (M := M) p q hpq).toLinearMap =
      CompactSupportDualCohomology.compactSupportEvaluation d (M := M) p q hpq := rfl

/-- Pointwise meaning of the canonical duality equivalence. -/
@[simp]
theorem compactSupportDualCohomologyEquiv_apply (p q : ℕ) (hpq : p + q = 2 * d)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p)
    (b : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q) :
    compactSupportDualCohomologyEquiv d p q hpq a b =
      CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a b := rfl

/-- The inverse equivalence realizes every actual functional with exactly
its prescribed evaluations. -/
@[simp]
theorem compactSupportDualCohomologyEquiv_symm_apply
    (p q : ℕ) (hpq : p + q = 2 * d)
    (L : Module.Dual ℚ (CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q))
    (b : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q) :
    CompactSupportDualCohomology.compactSupportEvaluation d p q hpq
        ((compactSupportDualCohomologyEquiv d p q hpq).symm L) b = L b :=
  congrArg (fun f => f b) ((compactSupportDualCohomologyEquiv d p q hpq).apply_symm_apply L)

/-- Every functional on complementary compact-support cohomology is
represented by a unique ordinary rational cohomology class. -/
theorem existsUnique_cohomology_of_compactSupportFunctional
    (p q : ℕ) (hpq : p + q = 2 * d)
    (L : Module.Dual ℚ (CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q)) :
    ∃! a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p,
      ∀ b, CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a b = L b := by
  refine ⟨(compactSupportDualCohomologyEquiv d p q hpq).symm L, ?_, ?_⟩
  · exact compactSupportDualCohomologyEquiv_symm_apply d p q hpq L
  · intro a ha
    apply (compactSupportDualCohomologyEquiv d p q hpq).injective
    apply LinearMap.ext
    intro b
    exact (ha b).trans (compactSupportDualCohomologyEquiv_symm_apply d p q hpq L b).symm

/-- Complementary compact-support tests distinguish ordinary rational
cohomology classes. -/
theorem cohomology_eq_iff_compactSupportEvaluation_eq
    (p q : ℕ) (hpq : p + q = 2 * d)
    (a a' : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p) :
    a = a' ↔ ∀ b, CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a b =
      CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a' b := by
  constructor
  · rintro rfl b
    rfl
  · intro h
    apply (compactSupportDualCohomologyEquiv d p q hpq).injective
    exact LinearMap.ext h

/-- Vanishing against all genuine compact-support tests detects a zero
ordinary cohomology class. -/
theorem cohomology_eq_zero_iff_compactSupportEvaluation_zero
    (p q : ℕ) (hpq : p + q = 2 * d)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p) :
    a = 0 ↔ ∀ b, CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a b = 0 := by
  rw [cohomology_eq_iff_compactSupportEvaluation_eq d p q hpq a 0]
  simp only [map_zero, LinearMap.zero_apply]

/-- A nonzero ordinary class has a complementary compact-support test
with nonzero actual cap evaluation. -/
theorem exists_compactSupport_test_of_ne_zero
    (p q : ℕ) (hpq : p + q = 2 * d)
    {a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p} (ha : a ≠ 0) :
    ∃ b, CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a b ≠ 0 := by
  classical
  apply not_forall.mp
  intro h
  exact ha ((cohomology_eq_zero_iff_compactSupportEvaluation_zero d p q hpq a).mpr h)

/-- Every nonzero compact-support class is detected, with value exactly
one, by an ordinary class. This uses field dual separation, not finite dimension. -/
theorem exists_cohomology_test_eq_one_of_ne_zero
    (p q : ℕ) (hpq : p + q = 2 * d)
    {b : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q} (hb : b ≠ 0) :
    ∃ a, CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a b = 1 := by
  obtain ⟨L, hL⟩ := Module.Projective.exists_dual_eq_one ℚ hb
  refine ⟨(compactSupportDualCohomologyEquiv d p q hpq).symm L, ?_⟩
  rw [compactSupportDualCohomologyEquiv_symm_apply]
  exact hL

/-- Ordinary cohomology tests also detect zero compact-support classes. -/
theorem compactSupport_eq_zero_iff_evaluation_zero
    (p q : ℕ) (hpq : p + q = 2 * d)
    (b : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q) :
    b = 0 ↔ ∀ a, CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a b = 0 := by
  constructor
  · rintro rfl a
    exact map_zero (CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a)
  · intro h
    by_contra hb
    obtain ⟨a, ha⟩ := exists_cohomology_test_eq_one_of_ne_zero d p q hpq hb
    exact one_ne_zero (ha.symm.trans (h a))

/-- The pairing separates compact-support classes as well as ordinary classes. -/
theorem compactSupport_eq_iff_evaluation_eq
    (p q : ℕ) (hpq : p + q = 2 * d)
    (b b' : CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q) :
    b = b' ↔ ∀ a, CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a b =
      CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a b' := by
  constructor
  · rintro rfl a
    rfl
  · intro h
    apply sub_eq_zero.mp
    apply (compactSupport_eq_zero_iff_evaluation_zero d p q hpq (b - b')).mpr
    intro a
    rw [map_sub, h a, sub_self]

/-- Equality may be tested on actual relative cohomology classes supported
on individual compact subsets, since every compact-support class has such
a representative. -/
theorem cohomology_eq_iff_compactSupportStage_evaluation_eq
    (p q : ℕ) (hpq : p + q = 2 * d)
    (a a' : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p) :
    a = a' ↔ ∀ (K : Compacts M)
      (b : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) (K : Set M)ᶜ q),
      CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a
          (CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of M) K q b) =
        CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a'
          (CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of M) K q b) := by
  constructor
  · rintro rfl K b
    rfl
  · intro h
    apply (cohomology_eq_iff_compactSupportEvaluation_eq d p q hpq a a').mpr
    intro b
    obtain ⟨K, c, rfl⟩ := CompactSupportColimit.compactSupportedCohomology_exists_stage
      (ModuleCat.of ℚ ℚ) (TopCat.of M) q b
    exact h K c

/-- A nonzero ordinary class is detected on one actual compact support,
with the test represented in the corresponding relative cohomology group. -/
theorem exists_compactSupport_stage_test_of_ne_zero
    (p q : ℕ) (hpq : p + q = 2 * d)
    {a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p} (ha : a ≠ 0) :
    ∃ (K : Compacts M)
      (b : Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) (K : Set M)ᶜ q),
      CompactSupportDualCohomology.compactSupportEvaluation d p q hpq a
        (CompactSupportCohomology.compactSupportCohomologyι (ModuleCat.of ℚ ℚ) (TopCat.of M) K q b) ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_compactSupport_test_of_ne_zero d p q hpq ha
  obtain ⟨K, c, rfl⟩ := CompactSupportColimit.compactSupportedCohomology_exists_stage
    (ModuleCat.of ℚ ℚ) (TopCat.of M) q b
  exact ⟨K, c, hb⟩

end SecondCountable

variable [CompactSpace M]

/-- On a compact complex manifold the same result uses its proved finite
chart-cover duality, without a separately supplied second-countability hypothesis. -/
def compactManifoldDualCohomologyEquiv (p q : ℕ) (hpq : p + q = 2 * d) :
    Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) p ≃ₗ[ℚ]
      Module.Dual ℚ (CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) q) :=
  Property.HasCanonicalPoincareDuality.compactSupportDualCohomologyEquiv d
    (Manifold.compactComplexManifold_hasCanonicalPoincareDuality d (M := M)) p q hpq

/-- The compact-case equivalence has the identical canonical evaluation map. -/
@[simp]
theorem compactManifoldDualCohomologyEquiv_toLinearMap
    (p q : ℕ) (hpq : p + q = 2 * d) :
    (compactManifoldDualCohomologyEquiv d (M := M) p q hpq).toLinearMap =
      CompactSupportDualCohomology.compactSupportEvaluation d (M := M) p q hpq := rfl

end

end OAI.AlgebraicTopology.Duality.Poincare.CompactSupportAnd
