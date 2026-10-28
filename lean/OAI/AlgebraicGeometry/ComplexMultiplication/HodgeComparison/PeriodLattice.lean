import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCoordinates
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Period Lattice -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodLattice.CM.Construction

noncomputable section

/-! The genuine degree-one Hodge coordinates define a finite-dimensional
complex period space, a discrete full lattice, and a compact Hausdorff quotient. -/

variable {ι : Type} [Fintype ι]
  (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (b : Module.Basis ι ℚ (V.rationalCohomology 1))

abbrev RationalH1PeriodSpace :=
  Fin (Module.finrank ℂ (Module.Dual ℂ (RationalCoordinates.CM.Construction.rationalH1HolomorphicCoordinates V b))) → ℂ

def rationalPeriodComplexEquiv :
    Module.Dual ℂ (RationalCoordinates.CM.Construction.rationalH1HolomorphicCoordinates V b) ≃ₗ[ℂ] RationalH1PeriodSpace V b :=
  (Module.finBasis ℂ (Module.Dual ℂ (RationalCoordinates.CM.Construction.rationalH1HolomorphicCoordinates V b))).equivFun

def rationalPeriodRealEquiv : (ι → ℝ) ≃ₗ[ℝ] RationalH1PeriodSpace V b :=
  (RationalCoordinates.CM.Construction.rationalH1PeriodEquiv V b).trans
    ((rationalPeriodComplexEquiv V b).restrictScalars ℝ)

def rationalPeriodProjection : (ι → ℂ) →L[ℂ] RationalH1PeriodSpace V b :=
  ⟨(rationalPeriodComplexEquiv V b).toLinearMap.comp
      (PeriodCoordinateDuality.CM.Construction.complexCoordinateEvaluation (RationalCoordinates.CM.Construction.rationalH1HolomorphicCoordinates V b)),
    LinearMap.continuous_of_finiteDimensional _⟩

theorem rationalPeriodProjection_real (r : ι → ℝ) :
    rationalPeriodProjection V b (fun i => (r i : ℂ)) = rationalPeriodRealEquiv V b r := rfl

def rationalPeriodBasis : Module.Basis ι ℝ (RationalH1PeriodSpace V b) :=
  (Pi.basisFun ℝ ι).map (rationalPeriodRealEquiv V b)

def rationalPeriodLattice : Submodule ℤ (RationalH1PeriodSpace V b) :=
  Submodule.span ℤ (Set.range (rationalPeriodBasis V b))

instance rationalPeriodLattice_discrete : DiscreteTopology (rationalPeriodLattice V b) := by
  unfold rationalPeriodLattice
  infer_instance

instance rationalPeriodLattice_full : IsZLattice ℝ (rationalPeriodLattice V b) := by
  unfold rationalPeriodLattice
  infer_instance

instance rationalPeriodLattice_add_discrete :
    DiscreteTopology (rationalPeriodLattice V b).toAddSubgroup :=
  rationalPeriodLattice_discrete V b

theorem rationalPeriodProjection_integer_mem (z : ι → ℤ) :
    rationalPeriodProjection V b (fun i => (z i : ℂ)) ∈ rationalPeriodLattice V b := by
  apply ((rationalPeriodBasis V b).mem_span_iff_repr_mem ℤ _).mpr
  intro i
  refine ⟨z i, ?_⟩
  have hz : rationalPeriodProjection V b (fun i => (z i : ℂ)) =
      rationalPeriodRealEquiv V b (fun i => (z i : ℝ)) := by
    simpa only [Complex.ofReal_intCast] using rationalPeriodProjection_real V b (fun i => (z i : ℝ))
  change algebraMap ℤ ℝ (z i) = (Pi.basisFun ℝ ι).repr
    ((rationalPeriodRealEquiv V b).symm
      (rationalPeriodProjection V b (fun i => (z i : ℂ)))) i
  rw [hz, LinearEquiv.symm_apply_apply, Pi.basisFun_repr, algebraMap_int_eq]
  rfl

abbrev RationalH1PeriodTorus := RationalH1PeriodSpace V b ⧸ (rationalPeriodLattice V b).toAddSubgroup

instance rationalH1PeriodTorus_compact : CompactSpace (RationalH1PeriodTorus V b) := by
  apply isCompact_univ_iff.mp
  have hc := IsZLattice.isCompact_range_of_periodic (rationalPeriodLattice V b)
    (QuotientAddGroup.mk : RationalH1PeriodSpace V b → RationalH1PeriodTorus V b)
    QuotientAddGroup.continuous_mk (by
      intro z w hw
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff w).mpr hw, add_zero])
  rwa [Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective] at hc

instance rationalH1PeriodTorus_t2 : T2Space (RationalH1PeriodTorus V b) := by
  let : DiscreteTopology (rationalPeriodLattice V b).toAddSubgroup := rationalPeriodLattice_discrete V b
  let : IsClosed ((rationalPeriodLattice V b).toAddSubgroup : Set (RationalH1PeriodSpace V b)) :=
    AddSubgroup.isClosed_of_discreteTopology
  infer_instance

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodLattice.CM.Construction
