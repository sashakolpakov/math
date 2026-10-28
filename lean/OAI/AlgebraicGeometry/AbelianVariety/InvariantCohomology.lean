import OAI.AlgebraicGeometry.AbelianVariety.AveragingDerivative
import OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham

/-! # Invariant Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianVariety.InvariantCohomology.Constructions.Exterior

noncomputable section

/-!
# Invariant forms in actual de Rham cohomology for ExteriorCohomology

Closed invariant forms map to their canonical de Rham classes. Haar averaging
descends through exact forms and is a left inverse to this map. Consequently
the canonical invariant-form map is injective in every degree.
-/

open scoped _root_.Manifold ContDiff _root_.Topology
open _root_.MeasureTheory

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ, E) ∞ G] [IsMulCommutative G]

def invariantClosedInclusion (n : ℕ) :
    InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E G n :=
  (InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) n).subtype.codRestrict
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E G n) (fun form => InvariantClosed.Constructions.ExteriorCohomology.invariantForms_closed form.val form.property)

def invariantDeRham (n : ℕ) :
    InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology E G n :=
  (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E G n).comp (invariantClosedInclusion n)

variable [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
  (μ : Measure G) [IsFiniteMeasure μ] [Measure.IsMulRightInvariant μ]

def averageClosedToInvariant (n : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E G n →ₗ[ℂ] InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) n :=
  ((Averaging.Constructions.ExteriorCohomology.averageForms μ).comp (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E G n).subtype).codRestrict
    (InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) n) (fun form => Averaging.Constructions.ExteriorCohomology.averageForms_mem μ form.val)

theorem averageClosedToInvariant_vanishes_on_exact (n : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms E G n ≤ LinearMap.ker (averageClosedToInvariant μ n) := by
  rintro form ⟨primitive, rfl⟩
  apply Subtype.ext
  change Averaging.Constructions.ExteriorCohomology.averageForms μ (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldIncomingExteriorDerivative E G n primitive) = 0
  cases n with
  | zero => exact map_zero (Averaging.Constructions.ExteriorCohomology.averageForms μ)
  | succ n => exact AveragingDerivative.Constructions.ExteriorCohomology.averageForms_d_eq_zero μ primitive

def deRhamAverage (n : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology E G n →ₗ[ℂ] InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) n :=
  ((Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms E G n).liftQ (averageClosedToInvariant μ n)
    (averageClosedToInvariant_vanishes_on_exact μ n)).comp
      (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormQuotientIso E G n).toLinearEquiv.toLinearMap

theorem deRhamAverage_invariantDeRham [IsProbabilityMeasure μ] (n : ℕ)
    (form : InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) n) :
    deRhamAverage μ n (invariantDeRham n form) = form := by
  change (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms E G n).liftQ (averageClosedToInvariant μ n)
      (averageClosedToInvariant_vanishes_on_exact μ n)
      ((Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormQuotientIso E G n).toLinearEquiv
        ((Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormQuotientIso E G n).toLinearEquiv.symm
          ((Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms E G n).mkQ (invariantClosedInclusion n form)))) = form
  rw [LinearEquiv.apply_symm_apply, Submodule.mkQ_apply, Submodule.liftQ_apply]
  apply Subtype.ext
  exact Averaging.Constructions.ExteriorCohomology.averageForms_of_invariant μ form.val form.property

theorem invariantDeRham_injective [IsProbabilityMeasure μ] (n : ℕ) :
    Function.Injective (invariantDeRham (E := E) (G := G) n) := by
  intro form other h
  have he := congrArg (deRhamAverage μ n) h
  rw [deRhamAverage_invariantDeRham, deRhamAverage_invariantDeRham] at he
  exact he

instance compactGroupHaar_isMulRightInvariant :
    (Averaging.Constructions.ExteriorCohomology.compactGroupHaar (E := E) (G := G)).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    have he : (fun h : G => h * g) = (fun h : G => g * h) := funext (fun h => mul_comm' h g)
    rw [he]
    exact Measure.IsMulLeftInvariant.map_mul_left_eq_self
      (μ := Averaging.Constructions.ExteriorCohomology.compactGroupHaar (E := E) (G := G)) g

theorem invariantDeRham_injective_compact (n : ℕ) :
    Function.Injective (invariantDeRham (E := E) (G := G) n) :=
  invariantDeRham_injective (Averaging.Constructions.ExteriorCohomology.compactGroupHaar (E := E) (G := G)) n

end

end OAI.AlgebraicGeometry.AbelianVariety.InvariantCohomology.Constructions.Exterior
