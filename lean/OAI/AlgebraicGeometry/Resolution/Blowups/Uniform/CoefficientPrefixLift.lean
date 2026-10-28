import OAI.AlgebraicGeometry.Resolution.Blowups.Global.BoundaryCoefficientSequenceLift
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.ClosedCarrierAtlasLift
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.CanonicalBoundaryComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.UniformIsoTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.CarrierComparisonIsoComposition
import OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceTraceCarrier
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonOpen

/-! # Coefficient Prefix Lift -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.CoefficientPrefixLift.Construction

noncomputable section

/-! Lift a complete recorded coefficient prefix, retaining every actual carrier embedding and both boundary traces. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

local instance uniformCoefficientLiftCarrierNoetherian {X : Scheme} [IsLocallyNoetherian X]
    (H : X.IdealSheafData) : IsLocallyNoetherian H.subscheme :=
  LocallyOfFiniteType.isLocallyNoetherian H.subschemeι

theorem exists_uniform_carrier_lift_of_bounded_coefficient_prefix (n : ℕ) :
    ∀ m : ℕ, ∀ (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
      (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J H : X.IdealSheafData),
      H ≠ ⊥ → Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H → ∀ [IsIntegral H.subscheme] [Smooth (H.subschemeι ≫ f)],
      H ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n → ∀ C : H.subscheme.IdealSheafData, C ≠ ⊥ →
      C ≤ GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J (n + 1) H.subschemeι →
      (∀ x : X, x ∈ H.support →
        ∃ A : GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H C (n + 1), Nonempty (Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction A) ∧
          ∃ p : PrimeSpectrum A.ring, A.map p = x) →
      ∀ {V : Scheme} {g : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {L : V.IdealSheafData}
        (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1).factorial H.subscheme (H.subschemeι ≫ f) C V g L),
      P.stepCount ≤ m → ∀ (β : Type) [Fintype β] (D : β → X.IdealSheafData),
      Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f (fun j : Option β => match j with | none => H | some l => D l) [Finset.univ] →
      ∀ T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β, P.HasIncidenceTrace β (fun l => (D l).comap H.subschemeι) T →
      (letI : Smooth g := P.endpoint_smooth; Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g L ((n + 1).factorial - 1) = ⊤) →
      ∃ (Y : Scheme) (h : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData) (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y h K)
        (r : V ⟶ Y), Q.CarrierComparison P H.subschemeι r ∧ Q.HasIncidenceTrace β D T ∧
          Q.HasIncidenceTrace (Option β) (fun j : Option β => match j with | none => H | some l => D l) T.adjoinCarrier ∧
          (letI : Smooth h := Q.endpoint_smooth; Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf h K n = ⊤) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro X _ _ f _ J H hH hlocal _ _ htangent C hC hupp hcharts V g L P hsize β _ D DA T htrace hterminal
      classical
      cases P with
      | stop =>
          cases T with
          | step => exact False.elim htrace
          | stop =>
              exact ⟨X, f, J, .stop, H.subschemeι, ⟨inferInstance, rfl, rfl⟩, ⟨DA.dropFirst⟩, ⟨DA⟩,
                GlobalCoefficient.Terminal.Construction.global_retained_coefficient_terminal_clears_order f J H C n htangent hupp hcharts hterminal⟩
      | blowup K hK hb hperm hs hbl tail =>
          cases T with
          | stop => exact False.elim htrace
          | step F trace =>
              obtain ⟨BA, hBA⟩ := htrace.1
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
              have hBA' : ∃ B : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (H.subschemeι ≫ f) (I.comap H.subschemeι)
                  (fun l => (D l).comap H.subschemeι), ∀ i, B.divided i = F := by
                rw [hIK]
                exact ⟨BA, hBA⟩
              obtain ⟨BA', hBA'⟩ := hBA'
              obtain ⟨AA, hAA⟩ := DA.dropFirst.exists_uniform_liftClosedCarrierCenter f I H hH hlocal hHI D BA' F hBA'
              obtain ⟨AAfull, hAAfull⟩ := AA.exists_adjoin_uniform_boundary_component F hAA H hHI DA
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
              let C' := GlobalCoefficient.Transform.Construction.globalRetainedCoefficientTransform I H C hI (n + 1)
              have hC' : C' ≠ ⊥ := GlobalCoefficient.Upper.Construction.globalRetainedCoefficientTransform_ne_bot f I H hI hH hlocal hHI C (n + 1) hC hCperm
              have hupp' := GlobalCoefficient.Upper.Construction.globalRetainedCoefficientTransform_le_intrinsic f I J H hI hH hlocal hHI hIH (n + 1) hp C hupp
              have hcharts' := Global.RetractedCoefficientCoverTransform.Construction.global_retracted_coefficient_charts_after_blowup f I J H hI hHI C (n + 1) hcharts hCperm
              obtain ⟨e, hemb, he, hcoeff⟩ := GlobalCoefficient.EmbeddingIso.Construction.exists_globalRetainedCoefficientTransform_embedding_iso
                f I H hI hH hlocal hHI K hK hIK C (n + 1)
              let D' := CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D
              have hDe (l : Option β) : ((D' l).comap H'.subschemeι).comap e.hom =
                  CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary K hK (fun j => (D j).comap H.subschemeι) l :=
                CanonicalBoundaryComparison.Construction.carrier_blowup_embedding_iso_uniform_canonicalBoundary f I H hI K hK hIK e hemb D F AA hAA BA hBA l
              let AH := (BA.blowupBoundary hK).transportIso
                (H'.subschemeι ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)) (fun l => (D' l).comap H'.subschemeι) e he hDe
              have htail : tail.HasIncidenceTrace (Option β)
                  (fun l => ((D' l).comap H'.subschemeι).comap e.hom) trace := by
                rw [funext hDe]
                exact htrace.2
              obtain ⟨W, k, M, U, r, hU, comparison, hr⟩ := tail.exists_uniform_iso_transport
                (H'.subschemeι ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)) C' hC' e he hcoeff
                (fun l => (D' l).comap H'.subschemeι) AH trace htail
              let : IsIso r := hr
              have hcount := comparison.stepCount_eq U tail e.hom r
              have hlt : U.stepCount < m := by
                change tail.stepCount + 1 ≤ m at hsize
                rw [hcount]
                omega
              have htU : letI : Smooth k := U.endpoint_smooth
                  Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf k M ((n + 1).factorial - 1) = ⊤ := by
                apply comparison.terminal_order_of_endpoint_cover U tail e.hom r _ _ hterminal
                intro x _
                refine ⟨inv r x, ?_⟩
                change (inv r ≫ r) x = x
                rw [IsIso.inv_hom_id]
                rfl
              have Afull' : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
                  (fun j : Option (Option β) => match j with | none => H' | some l => D' l) [Finset.univ] := by
                convert AAfull.blowupBoundaryWithCarrier hI using 1
              obtain ⟨Y, h, L', R, s, hcomp, hR, hRfull, htR⟩ := ih U.stepCount hlt (GlobalBlowup.Data.Construction.globalBlowup I hI)
                (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) H' hH' hlocal'
                htangent' C' hC' hupp' hcharts' U le_rfl (Option β) D'
                (by convert Afull' using 1; funext j; cases j <;> rfl) trace hU htU
              have hcomp' := hcomp.comp_iso R U H'.subschemeι s tail e.hom r comparison
              rw [hemb] at hcomp'
              refine ⟨Y, h, L', .blowup I hI (Nat.succ_pos n) hp inferInstance hblX R, r ≫ s,
                ⟨inferInstance, rfl, hIK, rfl, hcomp'⟩, ⟨⟨AA, hAA⟩, hR⟩, ?_, htR⟩
              refine ⟨⟨AAfull, hAAfull⟩, ?_⟩
              apply Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.HasIncidenceTrace.carrier_to_canonical (H := H) hI D R trace.adjoinCarrier
              convert hRfull using 1
              funext j
              cases j <;> rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.CoefficientPrefixLift.Construction
