import OAI.Analysis.HodgeTheory.Decomposition.VectorRepresentativeAE
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Compact Representative -/

namespace OAI.Analysis.HodgeTheory.Decomposition.CompactRepresentative.Constructions

noncomputable section

/-! A smooth representative of a compactly localized L² field is itself
compactly supported and therefore gives a genuine Schwartz representative. -/

open _root_.MeasureTheory Set
open scoped SchwartzMap ContDiff
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem vectorContinuousRepresentative_compact (g : 𝓢(E, ℂ)) (hgc : HasCompactSupport g)
    (u : Lp F 2 (volume : Measure E)) (v : E → F) (hv : Continuous v)
    (hveq : v =ᵐ[volume] AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g u) : HasCompactSupport v := by
  have hzero : v =ᵐ[volume.restrict (tsupport g)ᶜ] (fun _ => (0 : F)) := by
    apply (ae_restrict_iff' (isClosed_tsupport g).measurableSet.compl).mpr
    filter_upwards [hveq, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply_coe g u] with x hx hmul hs
    change x ∉ tsupport g at hs
    rw [hx, hmul, image_eq_zero_of_notMem_tsupport hs, zero_smul]
  have hpoint : EqOn v (fun _ => (0 : F)) (tsupport g)ᶜ :=
    Measure.eqOn_open_of_ae_eq hzero (isClosed_tsupport g).isOpen_compl hv.continuousOn continuousOn_const
  exact HasCompactSupport.intro hgc (fun x hx => hpoint hx)

def vectorSmoothRepresentativeSchwartz (g : 𝓢(E, ℂ)) (hgc : HasCompactSupport g)
    (u : Lp F 2 (volume : Measure E)) (v : BoundedContinuousFunction E F)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (v : E → F))
    (hveq : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv.CM.Construction.boundedFunctionDistribution v = (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g u : TemperedDistribution E F)) : 𝓢(E, F) :=
  (vectorContinuousRepresentative_compact g hgc u v v.continuous
    (VectorRepresentativeAE.Constructions.vectorBoundedFunctionDistribution_eq_lp_ae v _ hveq)).toSchwartzMap hv

theorem vectorSmoothRepresentativeSchwartz_toLp (g : 𝓢(E, ℂ)) (hgc : HasCompactSupport g)
    (u : Lp F 2 (volume : Measure E)) (v : BoundedContinuousFunction E F)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (v : E → F))
    (hveq : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv.CM.Construction.boundedFunctionDistribution v = (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g u : TemperedDistribution E F)) :
    (vectorSmoothRepresentativeSchwartz g hgc u v hv hveq).toLp 2 volume = AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g u := by
  apply Lp.ext
  exact ((vectorSmoothRepresentativeSchwartz g hgc u v hv hveq).coeFn_toLp 2 volume).trans
    (VectorRepresentativeAE.Constructions.vectorBoundedFunctionDistribution_eq_lp_ae v _ hveq)

end

end OAI.Analysis.HodgeTheory.Decomposition.CompactRepresentative.Constructions
