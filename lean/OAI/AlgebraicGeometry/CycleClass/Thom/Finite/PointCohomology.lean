import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SupportHomologySpanning
import OAI.AlgebraicGeometry.CycleClass.Thom.CompactPointIntegration

/-! # Point Cohomology -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Finite.PointCohomology.Constructions

/-! Canonical point classes form the dual basis on an actual finite support. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDual.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.CompactPointIntegration.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

theorem pointClass_insert_self (K : Set M) (U : Opens M) (x : U) (hx : x.val ∈ K)
    (hUK : ∀ y : U, y.val ∈ K → y = x) :
    AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of M) Kᶜ (2 * d)
      (CompactPointIntegration.Constructions.compactPointClass d K x.val hx)
      (ProperImage.FiniteFundamental.Constructions.Construction.finiteSupportLocalInsertion K U x hUK (2 * d)
        (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := U) x)) = 1 := by
  rw [CompactPointIntegration.Constructions.compactPointClass, AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation_naturality]
  exact (congrArg (AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of M) ({x.val}ᶜ) (2 * d)
    (CanonicalLocalDual.Constructions.canonicalLocalDual d x.val)) (ProperImage.FiniteFundamental.Constructions.Construction.finiteSupportLocalInsertion_fundamental_self d K U x hx hUK)).trans
    (CanonicalLocalDual.Constructions.canonicalLocalDual_integralEvaluation d x.val)

omit [T2Space M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M] in
theorem pointClass_insert_other (K : Set M) (U : Opens M) (x : U)
    (hUK : ∀ y : U, y.val ∈ K → y = x) (z : M) (hz : z ∈ K) (hzx : z ≠ x.val) :
    AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of M) Kᶜ (2 * d)
      (CompactPointIntegration.Constructions.compactPointClass d K z hz)
      (ProperImage.FiniteFundamental.Constructions.Construction.finiteSupportLocalInsertion K U x hUK (2 * d)
        (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := U) x)) = 0 := by
  rw [CompactPointIntegration.Constructions.compactPointClass, AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation_naturality]
  have h := ConcreteCategory.congr_hom
    (ProperImage.FiniteFundamental.Constructions.Construction.finiteSupportLocalInsertion_to_other K U x hUK z hz hzx (2 * d))
    (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := U) x)
  exact (congrArg (AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of M) ({z}ᶜ) (2 * d)
    (CanonicalLocalDual.Constructions.canonicalLocalDual d z)) h).trans (map_zero _)

theorem cohomology_eq_point_sum (K : Set M) [Fintype K] (U : K → Opens M)
    (hxU : ∀ x : K, x.val ∈ U x)
    (hUK : ∀ (x : K) (y : U x), y.val ∈ K → y.val = x.val)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) Kᶜ (2 * d)) :
    c = ∑ x : K,
      AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of M) Kᶜ (2 * d) c
        (ProperImage.FiniteFundamental.Constructions.Construction.finiteSupportLocalInsertion K (U x) ⟨x.val, hxU x⟩
          (fun y hy => Subtype.ext (hUK x y hy)) (2 * d)
          (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := U x) ⟨x.val, hxU x⟩)) •
      CompactPointIntegration.Constructions.compactPointClass d K x.val x.property := by
  classical
  apply (AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalUniversalCoefficientEquiv (TopCat.of M) Kᶜ (2 * d)).injective
  apply SupportHomologySpanning.Constructions.functional_ext d K U hxU hUK
  intro x
  change AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of M) Kᶜ (2 * d) c _ =
    AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of M) Kᶜ (2 * d) _ _
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single x]
  · rw [pointClass_insert_self d K (U x) ⟨x.val, hxU x⟩ x.property
      (fun y hy => Subtype.ext (hUK x y hy)), mul_one]
  · intro y _ hyx
    have hv : y.val ≠ x.val := fun he => hyx (Subtype.ext he)
    rw [pointClass_insert_other d K (U x) ⟨x.val, hxU x⟩
      (fun z hz => Subtype.ext (hUK x z hz)) y.val y.property hv, mul_zero]
  · simp

end AlgebraicGeometry.CycleClass.Thom.Finite.PointCohomology.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.Finite.PointCohomology.Constructions.LocalCoefficients

/-! Actual restrictions on isolating neighborhoods determine finite point coefficients. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDual.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.CompactPointIntegration.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Finite.PointCohomology.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem isolationMapsTo {M : Type} [TopologicalSpace M] (K : Set M) (U : Opens M) (x : U)
    (hUK : ∀ y : U, y.val ∈ K → y = x) :
    Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) ({x}ᶜ) Kᶜ :=
  fun y hy h => hy (hUK y h)

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M]

omit [T2Space M] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 M] in
theorem local_coefficient (K : Set M) (U : Opens M) (x : U)
    (hUK : ∀ y : U, y.val ∈ K → y = x)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) Kᶜ (2 * d))
    (w : ℚ)
    (hc : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) (isolationMapsTo K U x hUK) (2 * d) c =
        w • CanonicalLocalDual.Constructions.canonicalLocalDual d x) :
    AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation (TopCat.of M) Kᶜ (2 * d) c
      (ProperImage.FiniteFundamental.Constructions.Construction.finiteSupportLocalInsertion K U x hUK (2 * d)
        (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := U) x)) = w := by
  have h := AlgebraicTopology.Duality.Poincare.RelativeUniversalCoefficient.relativeRationalHomologyEvaluation_naturality
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) (isolationMapsTo K U x hUK)
    (2 * d) c (Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (M := U) x)
  refine h.symm.trans ?_
  rw [hc, map_smul, LinearMap.smul_apply, CanonicalLocalDual.Constructions.canonicalLocalDual_integralEvaluation,
    smul_eq_mul, mul_one]

theorem cohomology_eq_sum_of_local (K : Set M) [Fintype K] (U : K → Opens M)
    (hxU : ∀ x : K, x.val ∈ U x)
    (hUK : ∀ (x : K) (y : U x), y.val ∈ K → y.val = x.val)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) Kᶜ (2 * d)) (w : K → ℚ)
    (hc : ∀ x : K, AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U x : Set M))
      (isolationMapsTo K (U x) ⟨x.val, hxU x⟩ (fun y hy => Subtype.ext (hUK x y hy)))
      (2 * d) c = w x • CanonicalLocalDual.Constructions.canonicalLocalDual d (⟨x.val, hxU x⟩ : U x)) :
    c = ∑ x : K, w x • CompactPointIntegration.Constructions.compactPointClass d K x.val x.property := by
  classical
  refine (cohomology_eq_point_sum d K U hxU hUK c).trans ?_
  apply Finset.sum_congr rfl
  intro x _
  rw [local_coefficient d K (U x) ⟨x.val, hxU x⟩
    (fun y hy => Subtype.ext (hUK x y hy)) c (w x) (hc x)]

end AlgebraicGeometry.CycleClass.Thom.Finite.PointCohomology.Constructions.LocalCoefficients

end

end OAI
