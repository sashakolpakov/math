import OAI.RepresentationTheory.Theta.Geometric.Torus.Manifold
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Derivative -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus

noncomputable section

/-! The derivative of the literal quotient projection in its translation
charts is the identity. -/

open scoped _root_.Manifold ContDiff

variable (Φ : Data.CM.ProjectivePeriodData)

theorem Data.CM.ProjectivePeriodData.periodProjection_mfderiv (z : Φ.space) :
    mfderiv 𝓘(ℂ, Φ.space) 𝓘(ℂ, Φ.space)
      (QuotientAddGroup.mk : Φ.space → Φ.periodTorus) z = ContinuousLinearMap.id ℂ Φ.space := by
  have hd := (Φ.periodProjection_contMDiff z).mdifferentiableAt (by simp)
  have hh : HasFDerivAt (fun w : Φ.space =>
      Φ.periodChart (QuotientAddGroup.mk z) (QuotientAddGroup.mk w))
      (ContinuousLinearMap.id ℂ Φ.space) z :=
    ((hasFDerivAt_id z).add_const
      (Φ.periodChart (QuotientAddGroup.mk z) (QuotientAddGroup.mk z) - z)).congr_of_eventuallyEq
      (Φ.periodSection_eventuallyEq _ (Φ.periodChart_symm _) z (Φ.mem_periodChart_source _))
  simp only [mfderiv, hd, ↓reduceIte, writtenInExtChartAt, mfld_simps,
    fderivWithin_univ]
  exact hh.fderiv

end

end OAI.RepresentationTheory.Theta.Geometric.Torus
