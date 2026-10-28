import OAI.AlgebraicGeometry.Resolution.Blowups.Global.TangentComparisonNeighborhood
import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CongruenceSupport

/-! # Tangent Blowup Congruence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Intrinsic tangent congruence persists through an actual global permissible blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem IdealSheaf.CongruentMaps.Construction.IdealSheafCongruent.globalBlowupMapTo
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (q r : Y ⟶ X) [Etale q] [Etale r] (hqf : q ≫ f = g) (hrf : r ≫ f = g)
    (I J : X.IdealSheafData) (K : Y.IdealSheafData)
    (hq : I.comap q = K) (hr : I.comap r = K) (hI : I ≠ ⊥) (hK : K ≠ ⊥)
    (n : ℕ) (hp : J ≤ I ^ (n + 1)) [Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)]
    (hcongr : IdealSheaf.CongruentMaps.Construction.IdealSheafCongruent q r (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n)) :
    IdealSheaf.CongruentMaps.Construction.IdealSheafCongruent (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I K hq hI hK) (GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo r I K hr hI hK)
      (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI (n + 1)) n) := by
  apply IdealSheaf.CongruentMaps.Construction.IdealSheafCongruent.of_support_neighborhoods
  rintro x (hx | hx)
  · rw [Scheme.IdealSheafData.support_comap] at hx
    exact Global.TangentComparisonNeighborhood.Construction.globalBlowupMapTo_tangent_neighborhood f g q r hqf hrf I J K hq hr hI hK n hp hcongr x hx
  · rw [Scheme.IdealSheafData.support_comap] at hx
    obtain ⟨W, j, hj, hxj, hc⟩ :=
      Global.TangentComparisonNeighborhood.Construction.globalBlowupMapTo_tangent_neighborhood f g r q hrf hqf I J K hr hq hI hK n hp hcongr.symm x hx
    exact ⟨W, j, hj, hxj, hc.symm⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
