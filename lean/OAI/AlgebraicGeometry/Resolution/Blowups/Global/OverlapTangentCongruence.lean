import OAI.AlgebraicGeometry.Resolution.Blowups.Global.OverlapComparisonMaps
import OAI.AlgebraicGeometry.Resolution.Blowups.NamedAffineSectionMap
import OAI.AlgebraicGeometry.Resolution.Blowups.CommonBlowupTangentComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CongruenceSections
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CongruenceLocal
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.DifferentialTransform

/-! # Overlap Tangent Congruence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.OverlapTangentCongruence.Construction

noncomputable section

/-! Tangent congruence propagates on the actual common open charts of a global permissible blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra Blowup.Overlap.Construction.blowupOverlapBaseAlgebra

theorem globalBlowupOverlapChart_tangent_congruent
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (q r : Y ⟶ X) (hqf : q ≫ f = g) (hrf : r ≫ f = g)
    (I J : X.IdealSheafData) (K : Y.IdealSheafData)
    (hq : I.comap q = K) (hr : I.comap r = K) (hI : I ≠ ⊥) (hK : K ≠ ⊥)
    (n : ℕ) (hp : J ≤ I ^ (n + 1)) [Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)]
    (hcongr : IdealSheaf.CongruentMaps.Construction.IdealSheafCongruent q r (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n))
    (U : X.affineOpens) (V : Y.affineOpens)
    (hqU : V.1 ≤ q ⁻¹ᵁ U.1) (hrU : V.1 ≤ r ⁻¹ᵁ U.1)
    (a : I.ideal U) (b c : K.ideal V)
    (hb : b.val = (q.appLE U.1 V.1 hqU).hom a.val)
    (hc : c.val = (r.appLE U.1 V.1 hrU).hom a.val) :
    IdealSheaf.CongruentMaps.Construction.IdealSheafCongruent
      (GlobalBlowup.OverlapChart.Construction.globalBlowupOverlapChart K hK V b c ≫ GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I K hq hI hK)
      (GlobalBlowup.OverlapChart.Construction.globalBlowupOverlapChart K hK V b c ≫ GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo r I K hr hI hK)
      (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) n) := by
  let : Algebra ℂ Γ(X, U) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra f U
  let : Algebra ℂ Γ(Y, V) := Blowups.Smooth.DifferentialIdealSheaf.Construction.affineComplexAlgebra g V
  let φ := NamedAffineSectionMap.Construction.affineOpenSectionAlgMapTo f g q hqf U V hqU
  let ψ := NamedAffineSectionMap.Construction.affineOpenSectionAlgMapTo f g r hrf U V hrU
  have hφ : (I.ideal U).map φ.toRingHom = K.ideal V :=
    (IdealSheaf.AffinePullback.Construction.idealSheaf_comap_ideal_of_le I q U V hqU).symm.trans (congrArg (fun L => L.ideal V) hq)
  have hψ : (I.ideal U).map ψ.toRingHom = K.ideal V :=
    (IdealSheaf.AffinePullback.Construction.idealSheaf_comap_ideal_of_le I r U V hrU).symm.trans (congrArg (fun L => L.ideal V) hr)
  obtain ⟨hT, hdiff⟩ := hcongr.appLE U V hqU hrU
  have hnew := CommonBlowupTangentComparison.Construction.commonBlowupChart_tangent_comparison ℂ (I.ideal U) (J.ideal U) a n (hp U)
    φ ψ (K.ideal V) hφ hψ b c hb hc hT hdiff
  let F := CommonBlowupChartMaps.Construction.commonBlowupChartLeft ℂ (I.ideal U) a φ (K.ideal V) hφ b c hb
  let G := CommonBlowupChartMaps.Construction.commonBlowupChartRight ℂ (I.ideal U) a ψ (K.ideal V) hψ b c hc
  let T := Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
    (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) n
  have hs : IdealSheaf.CongruentMaps.Construction.IdealSheafCongruent (Spec.map (CommRingCat.ofHom F.toRingHom))
      (Spec.map (CommRingCat.ofHom G.toRingHom)) (T.comap (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a)) := by
    rw [DifferentialTransform.Construction.globalBlowupControlledIdeal_differential_comap_reesChart]
    exact Affine.IdealSheafCongruence.Construction.idealSheafCongruent_Spec_of_congruence F.toRingHom G.toRingHom _ hnew.1 hnew.2.1
  have hout := hs.postcomp (GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a) T
  rw [OverlapComparisonMaps.Construction.globalBlowupOverlapChart_map_left q I K hq hI hK U V hqU a b c hb hφ,
    OverlapComparisonMaps.Construction.globalBlowupOverlapChart_map_right r I K hr hI hK U V hrU a b c hc hψ]
  exact hout

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.OverlapTangentCongruence.Construction
