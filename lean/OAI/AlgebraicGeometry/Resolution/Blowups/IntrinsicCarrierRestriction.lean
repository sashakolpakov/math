import OAI.AlgebraicGeometry.Resolution.Blowups.IdealSheaf.CarrierBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.PullbackCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.GlobalCoefficientEtalePullback
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.SequenceCoefficientPersistence

/-! # Intrinsic Carrier Restriction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IntrinsicCarrierRestriction.Construction

noncomputable section

/-! Smoothness, nonzero coefficients, and maximal contact persist on named native carrier restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem native_carrier_restriction_smooth
    {X V : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (H : X.IdealSheafData)
    [Smooth (H.subschemeι ≫ f)] (q : V ⟶ X) [Etale q]
    (g : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (H0 : V.IdealSheafData) (hg : q ≫ f = g) (hH : H.comap q = H0) :
    Smooth (H0.subschemeι ≫ g) := by
  subst H0
  subst g
  exact Blowups.Etale.PullbackCenter.Construction.idealSheaf_comap_etale_smooth_center f q H

theorem native_carrier_restriction_coefficient_ne_bot
    {X V : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J H : X.IdealSheafData)
    [IsIntegral H.subscheme] (d : ℕ) (hC : GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf f J d H.subschemeι ≠ ⊥)
    (q : V ⟶ X) [Etale q] (g : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth g] (J0 H0 : V.IdealSheafData)
    [Nonempty H0.subscheme] (hg : q ≫ f = g) (hJ : J.comap q = J0) (hH : H.comap q = H0) :
    GlobalCoefficient.CoefficientSheaf.Construction.smoothCoefficientIdealSheaf g J0 d H0.subschemeι ≠ ⊥ := by
  let p := IdealSheaf.CarrierBaseChange.Construction.idealSheafCarrierMapTo H H0 q hH
  have he := Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothCoefficientIdealSheaf_comap_etale_square f J d H.subschemeι H0.subschemeι q p
    (IdealSheaf.CarrierBaseChange.Construction.idealSheafCarrierMapTo_over H H0 q hH)
  rw [hJ, Global.SequenceCoefficientPersistence.Construction.smoothCoefficientIdealSheaf_structure_congr (q ≫ f) g hg] at he
  exact he ▸ Blowups.Etale.PullbackCenter.Construction.idealSheaf_comap_nonempty_etale_ne_bot p _ hC

theorem native_carrier_restriction_tangent
    {X V : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J H : X.IdealSheafData) (n : ℕ)
    (hT : H ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n) (q : V ⟶ X) [Etale q]
    (g : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth g] (J0 H0 : V.IdealSheafData)
    (hg : q ≫ f = g) (hJ : J.comap q = J0) (hH : H.comap q = H0) :
    H0 ≤ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g J0 n := by
  have he := Scheme.IdealSheafData.comap_mono q hT
  change H.comap q ≤ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).comap q at he
  rw [hH, Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothDifferentialIdealSheaf_comap_etale, hJ,
    DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr (q ≫ f) g hg] at he
  exact he

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IntrinsicCarrierRestriction.Construction
