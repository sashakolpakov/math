import OAI.Analysis.HodgeTheory.Decomposition.CompactRepresentative

/-! # Smooth Representative Support -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothRepresentativeSupport

noncomputable section

/-! The actual smooth Schwartz representative is supported in the original scalar localization cutoff. -/

open _root_.MeasureTheory Set
open scoped SchwartzMap ContDiff
open OAI.Analysis.HodgeTheory.Decomposition.CompactRepresentative.Constructions

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem vectorContinuousRepresentative_tsupport (g : 𝓢(E, ℂ))
    (u : Lp F 2 (volume : Measure E)) (v : E → F) (hv : Continuous v)
    (hveq : v =ᵐ[volume] ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g u) : tsupport v ⊆ tsupport g := by
  have hzero : v =ᵐ[volume.restrict (tsupport g)ᶜ] (fun _ => (0 : F)) := by
    apply (ae_restrict_iff' (isClosed_tsupport g).measurableSet.compl).mpr
    filter_upwards [hveq, ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply_coe g u] with x hx hmul hs
    change x ∉ tsupport g at hs
    rw [hx, hmul, image_eq_zero_of_notMem_tsupport hs, zero_smul]
  have hpoint : EqOn v (fun _ => (0 : F)) (tsupport g)ᶜ :=
    Measure.eqOn_open_of_ae_eq hzero (isClosed_tsupport g).isOpen_compl hv.continuousOn continuousOn_const
  apply closure_minimal _ (isClosed_tsupport g)
  intro x hx
  by_contra hs
  exact hx (hpoint hs)

variable [CompleteSpace F]

theorem vectorSmoothRepresentativeSchwartz_tsupport (g : 𝓢(E, ℂ)) (hg : HasCompactSupport g)
    (u : Lp F 2 (volume : Measure E)) (v : BoundedContinuousFunction E F)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (v : E → F))
    (hveq : ComplexMultiplication.HodgeComparison.SobolevInv.CM.Construction.boundedFunctionDistribution v = (ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g u : TemperedDistribution E F)) :
    tsupport (Analysis.HodgeTheory.Decomposition.CompactRepresentative.Constructions.vectorSmoothRepresentativeSchwartz g hg u v hv hveq) ⊆ tsupport g :=
  vectorContinuousRepresentative_tsupport g u v v.continuous
    (Analysis.HodgeTheory.Decomposition.VectorRepresentativeAE.Constructions.vectorBoundedFunctionDistribution_eq_lp_ae v _ hveq)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothRepresentativeSupport
