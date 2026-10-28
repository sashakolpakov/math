import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SequenceStepCountTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.Upper
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.RetractedCoefficientCoverTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.Terminal
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SequenceHypersurface

/-! # Sequence Lift -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.SequenceLift.Construction

noncomputable section

/-! Lift an entire given native coefficient resolution to an actual global ambient control sequence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

local instance coefficientLiftCarrierNoetherian {X : Scheme} [IsLocallyNoetherian X]
    (H : X.IdealSheafData) : IsLocallyNoetherian H.subscheme :=
  LocallyOfFiniteType.isLocallyNoetherian H.subschemeι

theorem exists_global_control_sequence_of_bounded_coefficient_sequence (n : ℕ) :
    ∀ m : ℕ, ∀ (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
      (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J H : X.IdealSheafData),
      H ≠ ⊥ → Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H → ∀ [IsIntegral H.subscheme] [Smooth (H.subschemeι ≫ f)],
      H ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n → ∀ C : H.subscheme.IdealSheafData, C ≠ ⊥ →
      C ≤ CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι →
      (∀ x : X, x ∈ H.support →
        ∃ A : FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H C (n + 1), Nonempty (Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction A) ∧
          ∃ p : PrimeSpectrum A.ring, A.map p = x) →
      ∀ T : Global.MonomialSequence.Construction.SmoothFixedControlSequence (n + 1).factorial H.subscheme (H.subschemeι ≫ f) C,
      T.stepCount ≤ m → Nonempty (Global.MonomialSequence.Construction.SmoothFixedControlSequence (n + 1) X f J) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro X _ _ f _ J H hH hlocal _ _ htangent C hC hupp hcharts T hsize
      cases T with
      | terminal hterminal =>
          have hclear := Terminal.Construction.global_retained_coefficient_terminal_clears_order f J H C n htangent hupp hcharts hterminal
          exact ⟨.terminal (by simpa only [Nat.add_sub_cancel] using hclear)⟩
      | blowup K hK hb hperm hs hbl tail =>
          let I := K.map H.subschemeι
          have hI : I ≠ ⊥ := ClosedCarrierCenters.Construction.closedCarrierCenter_ne_bot H.subschemeι K hK
          have hHI : H ≤ I := by
            rw [← Scheme.IdealSheafData.ker_subschemeι H]
            exact ClosedCarrierCenters.Construction.closedCarrierCenter_contains_kernel H.subschemeι K
          have hIK : I.comap H.subschemeι = K := ClosedCarrierCenters.Construction.idealSheaf_closed_comap_map H.subschemeι K
          let : Smooth (K.subschemeι ≫ (H.subschemeι ≫ f)) := hs
          let : Smooth (I.subschemeι ≫ f) := ClosedCarrierCenters.Construction.closedCarrierCenter_smooth f H.subschemeι K
          have hCperm : C ≤ (I.comap H.subschemeι) ^ (n + 1).factorial := by rw [hIK]; exact hperm
          have hp : J ≤ I ^ (n + 1) := FamilyCharts.Construction.global_center_permissible_of_coefficient_family_charts f I J H hHI C (n + 1)
            (fun x hx => by obtain ⟨A, _, p, hp⟩ := hcharts x hx; exact ⟨A, p, hp⟩) hCperm
          let hblX := Global.SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f I hI
          let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := hblX
          have hIH : I.comap H.subschemeι ≠ ⊥ := by rw [hIK]; exact hK
          let H' := GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1
          let : IsIntegral H'.subscheme :=
            Global.SmoothHypersurfaceBlowupIso.Construction.globalBlowup_smooth_hypersurface_controlled_isIntegral f I H hI hH hlocal hHI hIH
          have hH' : H' ≠ ⊥ := GlobalBlowup.Nonzero.Construction.globalBlowupControlledIdeal_ne_bot I H hI 1 hH
          have hlocal' := GlobalControlled.Principality.Construction.globalBlowupControlledIdeal_locallyPrincipal I H hI 1 (by simpa only [pow_one] using hHI) hlocal
          let : Smooth (H'.subschemeι ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)) :=
            Global.SmoothHypersurfaceTransform.Construction.globalBlowup_smooth_controlled_hypersurface f I H hI hH hlocal hHI
          have htangent' := Global.SequenceHypersurface.Construction.globalBlowup_hypersurface_tangent_le f I J H hI n hp htangent
          let C' := Transform.Construction.globalRetainedCoefficientTransform I H C hI (n + 1)
          have hC' : C' ≠ ⊥ := Upper.Construction.globalRetainedCoefficientTransform_ne_bot f I H hI hH hlocal hHI C (n + 1) hC hCperm
          have hupp' := Upper.Construction.globalRetainedCoefficientTransform_le_intrinsic f I J H hI hH hlocal hHI hIH (n + 1) hp C hupp
          have hcharts' := Global.RetractedCoefficientCoverTransform.Construction.global_retracted_coefficient_charts_after_blowup f I J H hI hHI C (n + 1) hcharts hCperm
          obtain ⟨e, he, hcoeff⟩ := Upper.Construction.exists_globalRetainedCoefficientTransform_specified_iso f I H hI hH hlocal hHI K hK hIK C (n + 1)
          obtain ⟨U, hU⟩ := tail.transport_iso_with_stepCount
            (H'.subschemeι ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)) C' hC' e he hcoeff
          have hlt : U.stepCount < m := by
            change tail.stepCount + 1 ≤ m at hsize
            rw [hU]
            omega
          obtain ⟨rest⟩ := ih U.stepCount hlt (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
            (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) H' hH' hlocal' htangent' C' hC' hupp' hcharts' U le_rfl
          exact ⟨.blowup I hI (Nat.succ_pos n) hp inferInstance hblX rest⟩

theorem exists_global_control_sequence_of_retained_coefficient_sequence
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J H : X.IdealSheafData) (hH : H ≠ ⊥)
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) [IsIntegral H.subscheme] [Smooth (H.subschemeι ≫ f)]
    (n : ℕ) (htangent : H ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n)
    (C : H.subscheme.IdealSheafData) (hC : C ≠ ⊥)
    (hupp : C ≤ CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι)
    (hcharts : ∀ x : X, x ∈ H.support →
      ∃ A : FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H C (n + 1), Nonempty (Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction A) ∧
        ∃ p : PrimeSpectrum A.ring, A.map p = x)
    (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence (n + 1).factorial H.subscheme (H.subschemeι ≫ f) C) :
    Nonempty (Global.MonomialSequence.Construction.SmoothFixedControlSequence (n + 1) X f J) :=
  exists_global_control_sequence_of_bounded_coefficient_sequence n T.stepCount X f J H hH hlocal
    htangent C hC hupp hcharts T le_rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.SequenceLift.Construction
