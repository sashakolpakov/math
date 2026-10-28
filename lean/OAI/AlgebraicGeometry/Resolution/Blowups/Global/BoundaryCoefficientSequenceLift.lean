import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.SequenceLift
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ContainedBoundaryComponent
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.Labels
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.IntegralStepCountTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.EmbeddingIso
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.AtlasIsoTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CarrierCenterAtlasLift
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.Upper
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.RetractedCoefficientCoverTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficient.Terminal
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SequenceHypersurface

/-! # Boundary Coefficient Sequence Lift -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.BoundaryCoefficientSequenceLift.Construction

noncomputable section

/-! Lift a given coefficient sequence while retaining its Cartier carrier as an additional ambient boundary component. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

local instance carrierBoundaryCoefficientLiftCarrierNoetherian {X : Scheme} [IsLocallyNoetherian X]
    (H : X.IdealSheafData) : IsLocallyNoetherian H.subscheme :=
  LocallyOfFiniteType.isLocallyNoetherian H.subschemeι

theorem exists_global_carrier_boundary_integral_sequence_of_bounded_coefficient_sequence (n : ℕ) :
    ∀ m : ℕ, ∀ (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
      (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J H : X.IdealSheafData),
      H ≠ ⊥ → Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H → ∀ [IsIntegral H.subscheme] [Smooth (H.subschemeι ≫ f)],
      H ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n → ∀ C : H.subscheme.IdealSheafData, C ≠ ⊥ →
      C ≤ GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι →
      (∀ x : X, x ∈ H.support →
        ∃ A : GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H C (n + 1), Nonempty (Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction A) ∧
          ∃ p : PrimeSpectrum A.ring, A.map p = x) →
      ∀ T : MonomialSequence.Construction.SmoothFixedControlSequence (n + 1).factorial H.subscheme (H.subschemeι ≫ f) C,
      T.stepCount ≤ m → ∀ (β : Type) [Fintype β] (D : β → X.IdealSheafData),
      MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f (fun j : Option β => match j with | none => H | some l => D l) [Finset.univ] → T.integralCenters →
      T.boundaryCompatible β (fun l => (D l).comap H.subschemeι) →
      ∃ U : MonomialSequence.Construction.SmoothFixedControlSequence (n + 1) X f J, U.integralCenters ∧ U.boundaryCompatible (Option β) (fun j : Option β => match j with | none => H | some l => D l) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro X _ _ f _ J H hH hlocal _ _ htangent C hC hupp hcharts T hsize β _ D DA hint hbound
      cases T with
      | terminal hterminal =>
          have hclear := GlobalCoefficient.Terminal.Construction.global_retained_coefficient_terminal_clears_order f J H C n htangent hupp hcharts hterminal
          refine ⟨.terminal (by simpa only [Nat.add_sub_cancel] using hclear), ?_, ?_⟩
          · change True
            trivial
          · change Nonempty (MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f (fun j : Option β => match j with | none => H | some l => D l) [Finset.univ])
            exact ⟨DA⟩
      | blowup K hK hb hperm hs hbl tail =>
          change IsIntegral K.subscheme ∧ tail.integralCenters at hint
          change Nonempty (CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (H.subschemeι ≫ f) K
            (fun l => (D l).comap H.subschemeι)) ∧
            tail.boundaryCompatible (Option β)
              (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary K hK (fun l => (D l).comap H.subschemeι)) at hbound
          let : IsIntegral K.subscheme := hint.1
          obtain ⟨BA⟩ := hbound.1
          let I := K.map H.subschemeι
          have hI : I ≠ ⊥ := ClosedCarrierCenters.Construction.closedCarrierCenter_ne_bot H.subschemeι K hK
          have hHI : H ≤ I := by
            rw [← Scheme.IdealSheafData.ker_subschemeι H]
            exact ClosedCarrierCenters.Construction.closedCarrierCenter_contains_kernel H.subschemeι K
          have hIK : I.comap H.subschemeι = K := ClosedCarrierCenters.Construction.idealSheaf_closed_comap_map H.subschemeι K
          let : Smooth (K.subschemeι ≫ (H.subschemeι ≫ f)) := hs
          let : Smooth (I.subschemeι ≫ f) := ClosedCarrierCenters.Construction.closedCarrierCenter_smooth f H.subschemeι K
          have hCperm : C ≤ (I.comap H.subschemeι) ^ (n + 1).factorial := by rw [hIK]; exact hperm
          have hp : J ≤ I ^ (n + 1) := GlobalCoefficient.FamilyCharts.Construction.global_center_permissible_of_coefficient_family_charts f I J H hHI C (n + 1)
            (fun x hx => by obtain ⟨A, _, p, hp⟩ := hcharts x hx; exact ⟨A, p, hp⟩) hCperm
          let : IsIntegral I.subscheme := CanonicalBoundaryComparison.Construction.closedCarrierCenter_isIntegral H.subschemeι K
          have BA' : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (H.subschemeι ≫ f) (I.comap H.subschemeι)
              (fun l => (D l).comap H.subschemeι) := by rw [hIK]; exact BA
          let AA := MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.liftClosedCarrierCenter f I H hH hlocal hHI D DA.dropFirst BA'
          let AAfull := AA.adjoin_boundary_component H hHI DA
          let hblX := SmoothCenterBlowup.Construction.globalBlowup_smooth_of_smooth_center f I hI
          let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := hblX
          have hIH : I.comap H.subschemeι ≠ ⊥ := by rw [hIK]; exact hK
          let H' := GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1
          let : IsIntegral H'.subscheme :=
            SmoothHypersurfaceBlowupIso.Construction.globalBlowup_smooth_hypersurface_controlled_isIntegral f I H hI hH hlocal hHI hIH
          have hH' : H' ≠ ⊥ := GlobalBlowup.Nonzero.Construction.globalBlowupControlledIdeal_ne_bot I H hI 1 hH
          have hlocal' := GlobalControlled.Principality.Construction.globalBlowupControlledIdeal_locallyPrincipal I H hI 1 (by simpa only [pow_one] using hHI) hlocal
          let : Smooth (H'.subschemeι ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)) :=
            SmoothHypersurfaceTransform.Construction.globalBlowup_smooth_controlled_hypersurface f I H hI hH hlocal hHI
          have htangent' := SequenceHypersurface.Construction.globalBlowup_hypersurface_tangent_le f I J H hI n hp htangent
          let C' := GlobalCoefficient.Transform.Construction.globalRetainedCoefficientTransform I H C hI (n + 1)
          have hC' : C' ≠ ⊥ := GlobalCoefficient.Upper.Construction.globalRetainedCoefficientTransform_ne_bot f I H hI hH hlocal hHI C (n + 1) hC hCperm
          have hupp' := GlobalCoefficient.Upper.Construction.globalRetainedCoefficientTransform_le_intrinsic f I J H hI hH hlocal hHI hIH (n + 1) hp C hupp
          have hcharts' := RetractedCoefficientCoverTransform.Construction.global_retracted_coefficient_charts_after_blowup f I J H hI hHI C (n + 1) hcharts hCperm
          obtain ⟨e, hemb, he, hcoeff⟩ := GlobalCoefficient.EmbeddingIso.Construction.exists_globalRetainedCoefficientTransform_embedding_iso
            f I H hI hH hlocal hHI K hK hIK C (n + 1)
          let D' := CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D
          have hDe (l : Option β) : ((D' l).comap H'.subschemeι).comap e.hom =
              CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary K hK (fun j => (D j).comap H.subschemeι) l :=
            GlobalCoefficient.EmbeddingIso.Construction.carrier_blowup_embedding_iso_canonicalBoundary f I H hI K hK hIK rfl e hemb D AA BA l
          let AH := (BA.blowupBoundary hK).transportIso
            (H'.subschemeι ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)) (fun l => (D' l).comap H'.subschemeι) e he hDe
          have htailB : tail.boundaryCompatible (Option β)
              (fun l => ((D' l).comap H'.subschemeι).comap e.hom) := by
            rw [funext hDe]
            exact hbound.2
          obtain ⟨U, hUint, hUB, hU⟩ := tail.transport_boundary_integral_iso_with_stepCount hint.2
            (H'.subschemeι ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)) C' hC' e he hcoeff
            (fun l => (D' l).comap H'.subschemeι) AH htailB
          have hlt : U.stepCount < m := by
            change tail.stepCount + 1 ≤ m at hsize
            rw [hU]
            omega
          have Afull' : MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
              (fun j : Option (Option β) => match j with | none => H' | some l => D' l) [Finset.univ] := by
            convert AAfull.blowupBoundaryWithCarrier hI using 1
          obtain ⟨rest, hrestInt, hrestB⟩ := ih U.stepCount hlt (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
            (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) H' hH' hlocal' htangent' C' hC' hupp' hcharts' U le_rfl
            (Option β) D' (by convert Afull' using 1; funext j; cases j <;> rfl) hUint hUB
          have hrestB' : rest.boundaryCompatible (Option (Option β))
              (fun j => match j with
                | none => GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1
                | some l => CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D l) := by
            convert hrestB using 1
            funext j
            cases j <;> rfl
          exact ⟨.blowup I hI (Nat.succ_pos n) hp inferInstance hblX rest,
            ⟨inferInstance, hrestInt⟩,
            ⟨⟨AAfull⟩, rest.boundaryCompatible_carrier_to_canonical (H := H) hI D hrestB'⟩⟩

theorem exists_global_carrier_boundary_integral_sequence_of_retained_coefficient_sequence
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J H : X.IdealSheafData) (hH : H ≠ ⊥)
    (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) [IsIntegral H.subscheme] [Smooth (H.subschemeι ≫ f)]
    (n : ℕ) (htangent : H ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n)
    (C : H.subscheme.IdealSheafData) (hC : C ≠ ⊥)
    (hupp : C ≤ GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι)
    (hcharts : ∀ x : X, x ∈ H.support →
      ∃ A : GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H C (n + 1), Nonempty (Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction A) ∧
        ∃ p : PrimeSpectrum A.ring, A.map p = x)
    (T : MonomialSequence.Construction.SmoothFixedControlSequence (n + 1).factorial H.subscheme (H.subschemeι ≫ f) C)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData)
    (A : MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f (fun j : Option β => match j with | none => H | some l => D l) [Finset.univ]) (hT : T.integralCenters)
    (hB : T.boundaryCompatible β (fun l => (D l).comap H.subschemeι)) :
    ∃ U : MonomialSequence.Construction.SmoothFixedControlSequence (n + 1) X f J, U.integralCenters ∧ U.boundaryCompatible (Option β) (fun j : Option β => match j with | none => H | some l => D l) :=
  exists_global_carrier_boundary_integral_sequence_of_bounded_coefficient_sequence n T.stepCount X f J H hH
    hlocal htangent C hC hupp hcharts T le_rfl β D A hT hB

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.BoundaryCoefficientSequenceLift.Construction
