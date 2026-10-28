import OAI.AlgebraicGeometry.Resolution.Blowups.Global.OverlapOrderPoint
import OAI.AlgebraicGeometry.Resolution.Blowups.CongruentAffineNeighborhood
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Principality

/-! # Tangent Comparison Neighborhood -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.TangentComparisonNeighborhood.Construction

noncomputable section

/-! Construct an actual congruent comparison neighborhood around every transformed order point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem globalBlowupMapTo_tangent_neighborhood
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (q r : Y ⟶ X) [Etale q] (hqf : q ≫ f = g) (hrf : r ≫ f = g)
    (I J : X.IdealSheafData) (K : Y.IdealSheafData)
    (hq : I.comap q = K) (hr : I.comap r = K) (hI : I ≠ ⊥) (hK : K ≠ ⊥)
    (n : ℕ) (hp : J ≤ I ^ (n + 1)) [Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)]
    (hcongr : IdealSheaf.CongruentMaps.Construction.IdealSheafCongruent q r (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n))
    (x : GlobalBlowup.Data.Construction.globalBlowup K hK)
    (hx : GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I K hq hI hK x ∈
      (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) n).support) :
    ∃ (W : Scheme) (j : W ⟶ GlobalBlowup.Data.Construction.globalBlowup K hK), IsOpenImmersion j ∧ x ∈ Set.range j ∧
      IdealSheaf.CongruentMaps.Construction.IdealSheafCongruent (j ≫ GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I K hq hI hK)
        (j ≫ GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo r I K hr hI hK)
        (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
          (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) n) := by
  have hover : GlobalBlowup.Data.Construction.globalBlowupToBase I hI (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I K hq hI hK x) =
      q (GlobalBlowup.Data.Construction.globalBlowupToBase K hK x) :=
    congrArg (fun m => m x) (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo_over q I K hq hI hK)
  have hy : GlobalBlowup.Data.Construction.globalBlowupToBase K hK x ∈ ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).comap q).support := by
    rw [Scheme.IdealSheafData.support_comap]
    change q (GlobalBlowup.Data.Construction.globalBlowupToBase K hK x) ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support
    rw [← hover]
    by_contra hn
    have hpres := OrderLocusPreservation.Construction.globalBlowup_orderComplement_preimage_le f I J hI (n + 1) (Nat.succ_pos n) hp
    simp only [Nat.add_sub_cancel] at hpres
    exact hpres hn hx
  obtain ⟨U, V, hqU, hrU, hxV, _⟩ := hcongr.exists_affine_pair (GlobalBlowup.Data.Construction.globalBlowupToBase K hK x) hy
  have hxU : GlobalBlowup.Data.Construction.globalBlowupToBase I hI (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I K hq hI hK x) ∈ U.1 := by
    rw [hover]
    exact hqU hxV
  obtain ⟨a, p, hpmap⟩ := GlobalControlled.Principality.Construction.exists_globalBlowupReesChart_over_affineOpen I hI U
    (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I K hq hI hK x) hxU
  obtain ⟨b, c, hb, hc, hxchart⟩ := OverlapOrderPoint.Construction.exists_globalBlowupOverlapChart_order_point f g q r hqf hrf I J K hq hr
    hI hK n hp hcongr U V hqU hrU a x hxV p hpmap.symm (hpmap.symm ▸ hx)
  exact ⟨_, GlobalBlowup.OverlapChart.Construction.globalBlowupOverlapChart K hK V b c, inferInstance, hxchart,
    OverlapTangentCongruence.Construction.globalBlowupOverlapChart_tangent_congruent f g q r hqf hrf I J K hq hr hI hK n hp hcongr
      U V hqU hrU a b c hb hc⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.TangentComparisonNeighborhood.Construction
