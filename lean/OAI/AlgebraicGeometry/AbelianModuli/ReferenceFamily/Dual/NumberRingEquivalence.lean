import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberCoefficients

/-! # Number Ring Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberRingEquivalence

noncomputable section

/-! Actual ring equivalences transport both dual-number coefficients. -/

def dualNumberRingEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    DualNumber R ≃+* DualNumber S where
  __ := NumberCoefficients.dualNumberRingMap e.toRingHom
  invFun := NumberCoefficients.dualNumberRingMap e.symm.toRingHom
  left_inv x := TrivSqZeroExt.ext (e.symm_apply_apply x.fst) (e.symm_apply_apply x.snd)
  right_inv x := TrivSqZeroExt.ext (e.apply_symm_apply x.fst) (e.apply_symm_apply x.snd)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberRingEquivalence
