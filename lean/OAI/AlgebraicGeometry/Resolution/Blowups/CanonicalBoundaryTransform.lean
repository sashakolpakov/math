import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.TransverseRegularity
import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.AdmissiblePreservation
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MixedBoundary

/-! # Canonical Boundary Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalBoundaryTransform.Construction

noncomputable section

/-! One native control-one transform for every old boundary label, with locally varying incidence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem blowup_boundary_control_one_eq_mixed
    {k : Type u} [Field k] (R : CommRingCat.{u}) [Algebra k R]
    (I : Ideal R) (a : I) {ι : Type v} (w : ι → R) (F : Finset ι)
    (hw : ∀ j ∈ F, w j ∈ I)
    (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of (Blowup.Charts.Construction.blowupChart I a))
      (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I a F w hw)) (j : ι) :
    ControlledTransform.Construction.blowupControlledTransform I (Ideal.span {w j}) 1 a =
      Ideal.span {MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I a F w hw (some j)} := by
  classical
  by_cases hj : j ∈ F
  · simpa only [MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily, dite_eq_left hj] using
      Coordinate.BoundaryTransform.Construction.blowup_principal_coordinate_controlledTransform I a ⟨w j, hw j hj⟩
  · have h := hboundary.distinct_component_colon (.of (Blowup.Charts.Construction.blowupChart I a)) (some j) none (by simp)
    simp only [MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily, dite_eq_right hj] at h ⊢
    rw [ControlledTransform.Construction.blowupControlledTransform, Ideal.map_span, Set.image_singleton,
      pow_one (Blowup.Charts.Construction.blowupChartConstants I a a.val)]
    exact h

theorem blowup_admissible_boundary_control_one_eq_mixed
    {k : Type u} [Field k] (R : CommRingCat.{u}) [Algebra k R]
    (I : Ideal R) (a : I) {ι : Type v} (w : ι → R) (F : Finset ι)
    (hw : ∀ j ∈ F, w j ∈ I) (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w)
    (hcenter : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I w F) (j : ι) :
    ControlledTransform.Construction.blowupControlledTransform I (Ideal.span {w j}) 1 a =
      Ideal.span {MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I a F w hw (some j)} :=
  blowup_boundary_control_one_eq_mixed R I a w F hw
    (MixedBoundary.AdmissiblePreservation.Construction.hasEtaleBoundaryCharts_mixed_admissible_blowup R I w F hw hboundary hcenter a) j

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

def globalBlowupCanonicalBoundary (I : X.IdealSheafData) (hI : I ≠ ⊥) {ι : Type v}
    (D : ι → X.IdealSheafData) : Option ι → (GlobalBlowup.Data.Construction.globalBlowup I hI).IdealSheafData
  | none => I.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)
  | some j => GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (D j) hI 1

theorem globalBlowupCanonicalBoundary_ne_bot (I : X.IdealSheafData) (hI : I ≠ ⊥)
    {ι : Type v} (D : ι → X.IdealSheafData) (hD : ∀ j, D j ≠ ⊥) :
    ∀ j, globalBlowupCanonicalBoundary I hI D j ≠ ⊥ := by
  intro j
  cases j with
  | none => exact GlobalBlowup.Nonzero.Construction.globalBlowup_totalIdeal_ne_bot I I hI hI
  | some j => exact GlobalBlowup.Nonzero.Construction.globalBlowupControlledIdeal_ne_bot I (D j) hI 1 (hD j)

theorem globalBlowupCanonicalBoundary_comap_reesChart
    (I : X.IdealSheafData) (hI : I ≠ ⊥) {ι : Type v}
    (D : ι → X.IdealSheafData) (F : Finset ι) (U : X.affineOpens)
    (w : ι → Γ(X, U)) (hD : ∀ j, (D j).ideal U = Ideal.span {w j})
    (hw : ∀ j ∈ F, w j ∈ I.ideal U) (d : I.ideal U)
    {k : Type u} [Field k] [Algebra k Γ(X, U)]
    (hb : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of (Blowup.Charts.Construction.blowupChart (I.ideal U) d))
      (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily (I.ideal U) d F w hw)) (j : Option ι) :
    (globalBlowupCanonicalBoundary I hI D j).comap (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U d) =
      Affine.QuotientKernel.Construction.affineQuotientKernel (Ideal.span {MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily (I.ideal U) d F w hw j}) := by
  cases j with
  | none =>
      rw [globalBlowupCanonicalBoundary, GlobalControlled.Factorization.Construction.totalIdeal_comap_globalBlowupReesChart,
        ExceptionalIdeal.Construction.blowupChart_extendedIdeal]
      rfl
  | some j =>
      rw [globalBlowupCanonicalBoundary, GlobalControlled.Chart.Construction.globalBlowupControlledIdeal_comap_reesChart, hD j]
      exact congrArg Affine.QuotientKernel.Construction.affineQuotientKernel
        (blowup_boundary_control_one_eq_mixed (.of Γ(X, U)) (I.ideal U) d w F hw hb j)

theorem global_canonical_boundary_monomial_transform_on_chart
    (I : X.IdealSheafData) (hI : I ≠ ⊥) {ι : Type u} [Fintype ι]
    (D : ι → X.IdealSheafData) (F : Finset ι) (a : ι → ℕ) (b : ℕ)
    (hb : b ≤ Boundary.MonomialSchedule.Construction.boundaryFaceWeight a F) (U : X.affineOpens)
    (w : ι → Γ(X, U)) (hD : ∀ j, (D j).ideal U = Ideal.span {w j})
    (hw : ∀ j ∈ F, w j ∈ I.ideal U) (d : I.ideal U)
    {k : Type u} [Field k] [Algebra k Γ(X, U)]
    (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of (Blowup.Charts.Construction.blowupChart (I.ideal U) d))
      (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily (I.ideal U) d F w hw)) :
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) hI b).comap
        (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U d) =
      (Global.MixedBoundary.Construction.boundaryMonomialSheaf (globalBlowupCanonicalBoundary I hI D)
        (Boundary.MonomialSchedule.Construction.boundaryScheduleExponents a b F)).comap (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U d) := by
  classical
  rw [GlobalControlled.Chart.Construction.globalBlowupControlledIdeal_comap_reesChart, Global.MixedBoundary.Construction.boundaryMonomialSheaf_local_equations D a U w hD,
    Global.MixedBoundary.Construction.boundaryMonomialSheaf_comap_open]
  simp_rw [globalBlowupCanonicalBoundary_comap_reesChart I hI D F U w hD hw d hboundary]
  rw [Global.MixedBoundary.Construction.boundaryMonomialSheaf_affineQuotientKernel]
  exact congrArg Affine.QuotientKernel.Construction.affineQuotientKernel
    (LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement_controlledTransform (I.ideal U) d F w hw a b hb)

theorem global_canonical_boundary_locally_monomial_transform_on_chart
    (I M : X.IdealSheafData) (hI : I ≠ ⊥) {ι : Type u} [Fintype ι]
    (D : ι → X.IdealSheafData) (F : Finset ι) (a : ι → ℕ) (b : ℕ)
    (hb : b ≤ Boundary.MonomialSchedule.Construction.boundaryFaceWeight a F) (U : X.affineOpens)
    (w : ι → Γ(X, U)) (hD : ∀ j, (D j).ideal U = Ideal.span {w j})
    (hM : M.ideal U = Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a})
    (hw : ∀ j ∈ F, w j ∈ I.ideal U) (d : I.ideal U)
    {k : Type u} [Field k] [Algebra k Γ(X, U)]
    (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of (Blowup.Charts.Construction.blowupChart (I.ideal U) d))
      (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily (I.ideal U) d F w hw)) :
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I M hI b).comap (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U d) =
      (Global.MixedBoundary.Construction.boundaryMonomialSheaf (globalBlowupCanonicalBoundary I hI D)
        (Boundary.MonomialSchedule.Construction.boundaryScheduleExponents a b F)).comap (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U d) := by
  classical
  rw [GlobalControlled.Chart.Construction.globalBlowupControlledIdeal_comap_reesChart, hM, Global.MixedBoundary.Construction.boundaryMonomialSheaf_comap_open]
  simp_rw [globalBlowupCanonicalBoundary_comap_reesChart I hI D F U w hD hw d hboundary]
  rw [Global.MixedBoundary.Construction.boundaryMonomialSheaf_affineQuotientKernel]
  exact congrArg Affine.QuotientKernel.Construction.affineQuotientKernel
    (LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement_controlledTransform (I.ideal U) d F w hw a b hb)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalBoundaryTransform.Construction
