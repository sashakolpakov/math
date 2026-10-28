import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.CarrierClearance
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.Permissibility
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.IntersectionCanonical
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.IntegralSequenceReplacement

/-! # Carrier Clearance Solver -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.CarrierClearanceSolver.Construction

noncomputable section

/-! A lower-dimensional solver on one global boundary carrier supplies actual full-boundary clearance. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_global_boundary_carrier_clearance_of_zero_coefficient
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J H : X.IdealSheafData) (hH : H ≠ ⊥)
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) [Smooth (H.subschemeι ≫ f)] (n : ℕ)
    (hC : GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι = ⊥)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData)
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f
      (fun j : Option β => match j with | none => H | some l => D l) [Finset.univ]) :
    ∃ U : Global.MonomialSequence.Construction.SmoothFixedControlSequence (n + 1) X f (Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J H (n + 1)),
      U.integralCenters ∧
      U.boundaryCompatible (Option β) (fun j : Option β => match j with | none => H | some l => D l) ∧
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (U.toBase ≫ f) (U.transformIdeal J (n + 1)) n ⊔ U.transformIdeal H 1 = ⊤ := by
  classical
  let K := Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J H (n + 1)
  have hK : K ≠ ⊥ := by
    intro hz
    have h : H ^ (n + 1) ≤ K := le_sup_right
    rw [hz] at h
    exact Integral.IdealSheafProducts.Construction.idealSheaf_pow_ne_bot H hH (n + 1) (le_bot_iff.mp h)
  have hzero : GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f K (n + 1) H.subschemeι = ⊥ := by
    rw [Global.CarrierAuxiliaryCoefficients.Construction.smoothCoefficientIdealSheaf_carrier_auxiliary, hC]
  let E : Option β → X.IdealSheafData := fun j => match j with | none => H | some l => D l
  have AH : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f H E := by
    simpa only [Intersection.Construction.boundaryIntersectionSheaf, Finset.sup_singleton] using A.intersectionCenterAtlas {none}
  obtain ⟨U, hUint, hUB⟩ := GlobalCoefficient.Permissibility.Construction.exists_boundary_integral_sequence_of_zero_coefficient f K H hK n E AH
    (Global.NormalPowerAuxiliary.Construction.smooth_carrier_le_auxiliary_tangent f J H hH hlocal n) hzero
  refine ⟨U, hUint, hUB, ?_⟩
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
    U.auxiliary_terminal_clearance (Nat.succ_pos n) J H rfl

theorem exists_global_boundary_carrier_clearance_of_lower_solver
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J H : X.IdealSheafData) (hH : H ≠ ⊥)
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) [IsIntegral H.subscheme] [Smooth (H.subschemeι ≫ f)] (n : ℕ)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData)
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f
      (fun j : Option β => match j with | none => H | some l => D l) [Finset.univ])
    (hsolve : ∀ C : H.subscheme.IdealSheafData, C ≠ ⊥ →
      ∃ T : Global.MonomialSequence.Construction.SmoothFixedControlSequence (n + 1).factorial H.subscheme (H.subschemeι ≫ f) C,
        T.boundaryCompatible β (fun l => (D l).comap H.subschemeι)) :
    ∃ U : Global.MonomialSequence.Construction.SmoothFixedControlSequence (n + 1) X f (Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J H (n + 1)),
      U.integralCenters ∧
      U.boundaryCompatible (Option β) (fun j : Option β => match j with | none => H | some l => D l) ∧
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (U.toBase ≫ f) (U.transformIdeal J (n + 1)) n ⊔ U.transformIdeal H 1 = ⊤ := by
  by_cases hC : GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι = ⊥
  · exact exists_global_boundary_carrier_clearance_of_zero_coefficient f J H hH hlocal n hC D A
  · let : IsLocallyNoetherian H.subscheme := LocallyOfFiniteType.isLocallyNoetherian H.subschemeι
    let : CompactSpace H.subscheme := QuasiCompact.compactSpace_of_compactSpace H.subschemeι
    obtain ⟨T, hTB⟩ := hsolve _ hC
    obtain ⟨S, hSint, hSB⟩ := T.exists_boundary_integral_replacement hC β
      (fun l => (D l).comap H.subschemeι) hTB
    exact CarrierClearance.Construction.exists_global_boundary_carrier_clearance_of_integral_coefficient_sequence
      f J H hH hlocal n hC S D A hSint hSB

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.CarrierClearanceSolver.Construction
