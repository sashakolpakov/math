import OAI.AlgebraicGeometry.Resolution.Blowups.Global.BoundaryCoefficientSequenceLift
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.NormalPowerAuxiliary
import OAI.AlgebraicGeometry.Resolution.Blowups.InitialRetractedCoefficientCover
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.AuxiliarySequence

/-! # Carrier Clearance -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.CarrierClearance.Construction

noncomputable section

/-! A given coefficient resolution on a global boundary carrier clears its strict transform from the ambient order locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_global_boundary_carrier_clearance_of_integral_coefficient_sequence
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J H : X.IdealSheafData) (hH : H ≠ ⊥)
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) [IsIntegral H.subscheme] [Smooth (H.subschemeι ≫ f)]
    (n : ℕ) (hC : GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι ≠ ⊥)
    (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence (n + 1).factorial H.subscheme (H.subschemeι ≫ f)
      (GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι))
    {β : Type} [Fintype β] (D : β → X.IdealSheafData)
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f
      (fun j : Option β => match j with | none => H | some l => D l) [Finset.univ])
    (hT : T.integralCenters) (hB : T.boundaryCompatible β (fun l => (D l).comap H.subschemeι)) :
    ∃ U : Global.MonomialSequence.Construction.SmoothFixedControlSequence (n + 1) X f (Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J H (n + 1)),
      U.integralCenters ∧
      U.boundaryCompatible (Option β) (fun j : Option β => match j with | none => H | some l => D l) ∧
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (U.toBase ≫ f) (U.transformIdeal J (n + 1)) n ⊔ U.transformIdeal H 1 = ⊤ := by
  let K := Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J H (n + 1)
  have hcoeff : GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f K (n + 1) H.subschemeι =
      GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι :=
    Global.CarrierAuxiliaryCoefficients.Construction.smoothCoefficientIdealSheaf_carrier_auxiliary f J H (n + 1)
  have hcharts := InitialRetractedCoefficientCover.Construction.exists_initial_retracted_global_coefficient_cover f K H hH hlocal (n + 1)
  rw [hcoeff] at hcharts
  obtain ⟨U, hUint, hUB⟩ := Global.BoundaryCoefficientSequenceLift.Construction.exists_global_carrier_boundary_integral_sequence_of_retained_coefficient_sequence
    f K H hH hlocal n (Global.NormalPowerAuxiliary.Construction.smooth_carrier_le_auxiliary_tangent f J H hH hlocal n)
    (GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι) hC hcoeff.symm.le hcharts T D A hT hB
  refine ⟨U, hUint, hUB, ?_⟩
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
    U.auxiliary_terminal_clearance (Nat.succ_pos n) J H rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.CarrierClearance.Construction
