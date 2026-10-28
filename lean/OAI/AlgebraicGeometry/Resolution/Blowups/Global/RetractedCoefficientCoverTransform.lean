import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ReducedReesEtale
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ReducedReesPointCover
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.RetractedCoefficientBlowupChart
import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.BlowupCover
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.AlgebraReduced

/-! # Retracted Coefficient Cover Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.RetractedCoefficientCoverTransform.Construction

noncomputable section

/-! Actual retracted coefficient charts cover the entire transformed carrier after a permissible blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem global_retracted_coefficient_charts_after_blowup
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (I J H : X.IdealSheafData) (hI : I ≠ ⊥)
    [Smooth (I.subschemeι ≫ f)] (hHI : H ≤ I) (C : H.subscheme.IdealSheafData) (b : ℕ)
    (hcharts : ∀ x : X, x ∈ H.support →
      ∃ T : GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H C b, Nonempty (Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction T) ∧
        ∃ p : PrimeSpectrum T.ring, T.map p = x)
    (hC : C ≤ (I.comap H.subschemeι) ^ b.factorial)
    (x : GlobalBlowup.Data.Construction.globalBlowup I hI) (hx : x ∈ (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).support) :
    ∃ T : GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1)
        (GlobalCoefficient.Transform.Construction.globalRetainedCoefficientTransform I H C hI b) b,
      Nonempty (Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction T) ∧ ∃ p : PrimeSpectrum T.ring, T.map p = x := by
  have hp : J ≤ I ^ b := GlobalCoefficient.FamilyCharts.Construction.global_center_permissible_of_coefficient_family_charts f I J H hHI C b
    (fun x hx => by obtain ⟨T, _, p, hp⟩ := hcharts x hx; exact ⟨T, p, hp⟩) hC
  have htotal : H.comap (GlobalBlowup.Data.Construction.globalBlowupToBase I hI) ≤ GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1 :=
    GlobalControlled.Ideal.Construction.totalIdeal_le_controlledIdealSheaf I H 1 (GlobalBlowup.Data.Construction.globalBlowupToBase I hI)
  have hbase := Scheme.IdealSheafData.support_antitone htotal hx
  rw [Scheme.IdealSheafData.support_comap] at hbase
  obtain ⟨T, ⟨F⟩, q, hq⟩ := hcharts (GlobalBlowup.Data.Construction.globalBlowupToBase I hI x) hbase
  let : Algebra.Smooth ℂ T.ring := by
    have hs : Smooth (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure T.ring) := T.ground ▸ inferInstanceAs (Smooth (T.map ≫ f))
    exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)
      (φ := CommRingCat.ofHom (algebraMap ℂ T.ring))).mp hs)
  let : IsNoetherianRing T.ring := Algebra.FiniteType.isNoetherianRing ℂ T.ring
  let : _root_.IsReduced T.ring := Blowups.Smooth.AlgebraReduced.Construction.smooth_algebra_isReduced ℂ
  let : Algebra ℚ T.ring := ((algebraMap ℂ T.ring).comp (algebraMap ℚ ℂ)).toAlgebra
  obtain ⟨L, hL⟩ := Affine.KernelOrderEquiv.Construction.exists_affineQuotientKernel (I.comap T.map)
  let K := (L.map (Ideal.Quotient.mk (Ideal.span {T.normal}))).map F.retraction.toRingHom
  have hKL : Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := T.ring) K = L := (F.center_equations I hHI L hL.symm).2
  have hK : I.comap T.map = Affine.QuotientKernel.Construction.affineQuotientKernel (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := T.ring) K) := by
    rw [hKL]
    exact hL.symm
  obtain ⟨i, P, hP⟩ := ReducedReesPointCover.Construction.exists_generated_globalReducedReesComparison_point I hI T.ring T.map
    (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) hK (EtaleLine.BlowupCover.Construction.etaleLineChartGenerator K) (EtaleLine.BlowupCover.Construction.etaleLineChartGenerator_span K) x q hq
  cases i with
  | none =>
      let a := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement (R := T.ring) K
      let j := ReducedReesComparison.Construction.globalReducedReesComparison I hI T.ring T.map (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) hK a
      have hHmap : (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).comap j = ⊤ := by
        have h := ReducedReesComparison.Construction.globalReducedReesComparison_controlledIdeal I H hI 1 (by simpa only [pow_one] using hHI)
          T.ring T.map (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) (Ideal.span {T.normal}) hK T.hypersurface a
        rw [F.normal_eq] at h
        change (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).comap j =
          Affine.QuotientKernel.Construction.affineQuotientKernel (ControlledTransform.Construction.blowupControlledTransform (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) (Ideal.span {a.val}) 1 a) at h
        rw [Coordinate.BoundaryTransform.Construction.blowup_principal_coordinate_controlledTransform, Blowups.Etale.CoefficientStep.Construction.blowupChartRatio_self,
          Ideal.span_singleton_one, DifferentialUnitGluing.Construction.affineQuotientKernel_top] at h
        exact h
      have hm : P ∈ ((GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).comap j).support := by
        rw [Scheme.IdealSheafData.support_comap]
        change j P ∈ (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).support
        exact (congrArg (fun y : GlobalBlowup.Data.Construction.globalBlowup I hI => y ∈ (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I H hI 1).support) hP).mpr hx
      rw [hHmap, Scheme.IdealSheafData.support_top] at hm
      exact hm.elim
  | some a =>
      let j := ReducedReesComparison.Construction.globalReducedReesComparison I hI T.ring T.map (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) hK (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator K a)
      let : Etale j := ReducedReesEtale.Construction.globalReducedReesComparison_etale I hI T.ring T.map (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) hK _
      let B := F.blowupChart I hI hHI hp hC K hK a j (ReducedReesComparison.Construction.globalReducedReesComparison_over I hI T.ring T.map _ hK _)
      exact ⟨B.1, ⟨B.2⟩, P, hP⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.RetractedCoefficientCoverTransform.Construction
