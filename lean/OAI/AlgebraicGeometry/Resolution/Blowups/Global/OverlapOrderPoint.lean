import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ComparisonChartPoint
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.OverlapTangentCongruence
import OAI.AlgebraicGeometry.Resolution.Blowups.CommonBlowupOrderNeighborhood
import OAI.AlgebraicGeometry.Resolution.Blowups.SpecifiedBlowupChartPoint
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ChartSupport

/-! # Overlap Order Point -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.OverlapOrderPoint.Construction

noncomputable section

/-! The common denominator open contains each actual transformed order point in the comparison source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra Blowup.Overlap.Construction.blowupOverlapBaseAlgebra

theorem exists_globalBlowupOverlapChart_order_point
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (q r : Y ⟶ X) [Etale q] (hqf : q ≫ f = g) (hrf : r ≫ f = g)
    (I J : X.IdealSheafData) (K : Y.IdealSheafData)
    (hq : I.comap q = K) (hr : I.comap r = K) (hI : I ≠ ⊥) (hK : K ≠ ⊥)
    (n : ℕ) (hp : J ≤ I ^ (n + 1)) [Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)]
    (hcongr : IdealSheaf.CongruentMaps.Construction.IdealSheafCongruent q r (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n))
    (U : X.affineOpens) (V : Y.affineOpens)
    (hqU : V.1 ≤ q ⁻¹ᵁ U.1) (hrU : V.1 ≤ r ⁻¹ᵁ U.1)
    (a : I.ideal U) (x : GlobalBlowup.Data.Construction.globalBlowup K hK) (hxV : GlobalBlowup.Data.Construction.globalBlowupToBase K hK x ∈ V.1)
    (p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart (I.ideal U) a))
    (hpx : GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I K hq hI hK x = GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a p)
    (hporder : GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a p ∈
      (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) n).support) :
    ∃ (b c : K.ideal V), b.val = (q.appLE U.1 V.1 hqU).hom a.val ∧
      c.val = (r.appLE U.1 V.1 hrU).hom a.val ∧
        x ∈ Set.range (GlobalBlowup.OverlapChart.Construction.globalBlowupOverlapChart K hK V b c) := by
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : Algebra ℂ Γ(Y, V) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra g V
  let : Algebra.Smooth ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra_smooth f U
  let φ := NamedAffineSectionMap.Construction.affineOpenSectionAlgMapTo f g q hqf U V hqU
  let ψ := NamedAffineSectionMap.Construction.affineOpenSectionAlgMapTo f g r hrf U V hrU
  have hφ : (I.ideal U).map φ.toRingHom = K.ideal V :=
    (IdealSheaf.AffinePullback.Construction.idealSheaf_comap_ideal_of_le I q U V hqU).symm.trans (congrArg (fun L => L.ideal V) hq)
  have hψ : (I.ideal U).map ψ.toRingHom = K.ideal V :=
    (IdealSheaf.AffinePullback.Construction.idealSheaf_comap_ideal_of_le I r U V hrU).symm.trans (congrArg (fun L => L.ideal V) hr)
  let b : K.ideal V := ⟨φ a.val, hφ ▸ Ideal.mem_map_of_mem φ.toRingHom a.property⟩
  let c : K.ideal V := ⟨ψ a.val, hψ ▸ Ideal.mem_map_of_mem ψ.toRingHom a.property⟩
  obtain ⟨P, hPx, hPp⟩ := ComparisonChartPoint.Construction.exists_globalBlowupMapTo_reesChart_point q I K hq hI hK U V hqU a b rfl hφ
    x hxV p hpx
  have hs : Smooth (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure (Blowup.Charts.Construction.blowupChart (I.ideal U) a)) :=
    (GlobalControlled.DifferentialBound.Construction.globalBlowupReesChart_complex_structure f I hI U a) ▸
      inferInstanceAs (Smooth (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)))
  let : Algebra.Smooth ℂ (Blowup.Charts.Construction.blowupChart (I.ideal U) a) := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hs)
  have hpalgebra : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ
      (ControlledTransform.Construction.blowupControlledTransform (I.ideal U) (J.ideal U) (n + 1) a) n ≤ p.asIdeal := by
    have he := congrArg (fun L => (L.support : Set (Spec (.of (Blowup.Charts.Construction.blowupChart (I.ideal U) a)))))
      (DifferentialTransform.Construction.globalBlowupControlledIdeal_differential_comap_reesChart f I J hI (n + 1) n U a)
    rw [Scheme.IdealSheafData.support_comap, Coefficient.ChartSupport.Construction.affineQuotientKernel_support] at he
    have hm : p ∈ PrimeSpectrum.zeroLocus (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal ℂ
        (ControlledTransform.Construction.blowupControlledTransform (I.ideal U) (J.ideal U) (n + 1) a) n) := by
      rw [← he]
      exact hporder
    exact hm
  have hφet : φ.toRingHom.Etale := q.etale_appLE U.2 V.2 hqU
  have hPorder := SpecifiedBlowupChartPoint.Construction.blowupChartMapTo_transformed_order_prime ℂ (I.ideal U) (J.ideal U) a n (hp U)
    φ hφet (K.ideal V) hφ b rfl p P hPp hpalgebra
  obtain ⟨Q, hQP⟩ := CommonBlowupOrderNeighborhood.Construction.commonBlowupChart_covers_transformed_order ℂ (I.ideal U) (J.ideal U) a n (hp U)
    φ ψ hφet (K.ideal V) hφ b c rfl rfl (hcongr.appLE U V hqU hrU).2 P hPorder
  refine ⟨b, c, rfl, rfl, Q, ?_⟩
  exact (congrArg (GlobalControlled.Chart.Construction.globalBlowupReesChart K hK V b) hQP).trans hPx

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.OverlapOrderPoint.Construction
