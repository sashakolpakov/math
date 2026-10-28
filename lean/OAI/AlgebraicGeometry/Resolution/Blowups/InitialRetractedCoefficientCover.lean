import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalCoefficientFamilyCharts
import OAI.AlgebraicGeometry.Resolution.Blowups.RetractedGlobalCoefficientChart
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ChartSupport
import OAI.AlgebraicGeometry.Resolution.Blowups.Finite.TypeRingDimensionBound

/-! # Initial Retracted Coefficient Cover -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.InitialRetractedCoefficientCover.Construction

noncomputable section

/-! Actual retracted coefficient charts through every point of a smooth native Cartier carrier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_initial_retracted_global_coefficient_cover
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J H : X.IdealSheafData) (hH : H ≠ ⊥)
    [Smooth (H.subschemeι ≫ f)] (hlocal : Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf H) (b : ℕ)
    (x : X) (hx : x ∈ H.support) :
    ∃ T : GlobalCoefficient.FamilyCharts.Construction.GlobalCoefficientFamilyChart f J H (GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J b H.subschemeι) b,
      Nonempty (Retracted.GlobalCoefficientChart.Construction.GlobalCoefficientFamilyRetraction T) ∧
        ∃ p : PrimeSpectrum T.ring, T.map p = x := by
  obtain ⟨T, q, hq⟩ := GlobalCoefficientFamilyCharts.Construction.exists_initial_global_coefficient_family_charts f J H hH hlocal b x hx
  let : Algebra.Smooth ℂ T.ring := by
    have hs : Smooth (ComplexAffineDifferentialIdeal.Construction.complexSpecStructure T.ring) := T.ground ▸ inferInstanceAs (Smooth (T.map ≫ f))
    exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)
      (φ := CommRingCat.ofHom (algebraMap ℂ T.ring))).mp hs)
  obtain ⟨d, hd⟩ := Finite.TypeRingDimensionBound.Construction.finiteType_ringKrullDim_bounded ℂ T.ring
  have hdim : ringKrullDim T.ring ≤ (d + 1 : ℕ) := hd.trans (by exact_mod_cast Nat.le_succ d)
  have hn : T.normal ∈ q.asIdeal := (T.normal_mem_iff q).mpr (hq.symm ▸ hx)
  obtain ⟨T', A, _, p, hp⟩ := RetractedGlobalCoefficientChart.Construction.exists_initial_retracted_global_coefficient_chart f T q hn d hdim
  exact ⟨T', ⟨A⟩, p, hp.trans hq⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.InitialRetractedCoefficientCover.Construction
