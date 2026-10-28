import OAI.RepresentationTheory.Theta.Geometric.Projective.DolbeaultEquiv
import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.PicardPeriodQuotient

/-! # Closed Form Picard Zero -/

namespace OAI.RepresentationTheory.Theta.Geometric.ClosedFormPicardZero

noncomputable section

/-! Exponentiating actual globally closed antiholomorphic one-forms
gives exactly the holomorphic line classes with vanishing integral Chern obstruction. -/

set_option backward.isDefEq.respectTransparency false

def closedFormPicardMap (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    ClosedPureDolbeaultMap.ClosedType01Forms V.analyticModel V.analyticSpace →+
      AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace :=
  (Holomorphic.PicardZero.holomorphicExponentialH1 V.analyticModel V.analyticSpace).comp
    (Projective.DolbeaultEquiv.closedType01HolomorphicH1Equiv V).toAddMonoidHom

theorem closedFormPicardMap_connecting (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : ClosedPureDolbeaultMap.ClosedType01Forms V.analyticModel V.analyticSpace) :
    AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting V.analyticModel V.analyticSpace (closedFormPicardMap V a) = 0 :=
  Holomorphic.PicardZero.holomorphicExponentialH1_connecting V.analyticModel V.analyticSpace _

theorem exists_closedForm_of_zeroChern (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
    (hu : AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting V.analyticModel V.analyticSpace u = 0) :
    ∃ a : ClosedPureDolbeaultMap.ClosedType01Forms V.analyticModel V.analyticSpace, closedFormPicardMap V a = u := by
  obtain ⟨v, hv⟩ := Holomorphic.PicardZero.exists_holomorphicH1_of_connecting_zero V.analyticModel V.analyticSpace u hu
  refine ⟨(Projective.DolbeaultEquiv.closedType01HolomorphicH1Equiv V).symm v, ?_⟩
  change Holomorphic.PicardZero.holomorphicExponentialH1 V.analyticModel V.analyticSpace
    (Projective.DolbeaultEquiv.closedType01HolomorphicH1Equiv V ((Projective.DolbeaultEquiv.closedType01HolomorphicH1Equiv V).symm v)) = u
  rw [AddEquiv.apply_symm_apply, hv]

theorem closedFormPicardMap_range (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    (closedFormPicardMap V).range =
      (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting V.analyticModel V.analyticSpace).ker := by
  ext u
  constructor
  · rintro ⟨a, rfl⟩
    exact closedFormPicardMap_connecting V a
  · exact exists_closedForm_of_zeroChern V u

theorem closedFormPicardMap_eq_zero_iff_period (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : ClosedPureDolbeaultMap.ClosedType01Forms V.analyticModel V.analyticSpace) :
    closedFormPicardMap V a = 0 ↔
      ∃ t : CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.IntegralConstantSheaf.integralConstantSheaf (TopCat.of V.analyticSpace)) 1,
        Projective.DolbeaultEquiv.closedType01HolomorphicH1Equiv V a = Holomorphic.PicardPeriodQuotient.holomorphicPeriodH1 V.analyticModel V.analyticSpace t := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := Holomorphic.PicardPeriodQuotient.exists_integralH1_of_exponential_zero V.analyticModel V.analyticSpace
      (Projective.DolbeaultEquiv.closedType01HolomorphicH1Equiv V a) h
    exact ⟨t, ht.symm⟩
  · rintro ⟨t, ht⟩
    change Holomorphic.PicardZero.holomorphicExponentialH1 V.analyticModel V.analyticSpace
      (Projective.DolbeaultEquiv.closedType01HolomorphicH1Equiv V a) = 0
    rw [ht]
    exact Holomorphic.PicardPeriodQuotient.holomorphicPeriodH1_exponential V.analyticModel V.analyticSpace t

end

end OAI.RepresentationTheory.Theta.Geometric.ClosedFormPicardZero
