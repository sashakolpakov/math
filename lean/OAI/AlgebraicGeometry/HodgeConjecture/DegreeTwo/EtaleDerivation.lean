import Mathlib.RingTheory.Etale.Kaehler

/-! # Etale Derivation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.EtaleDerivation.Constructions

noncomputable section

/-!
# DegreeTwo: extend actual derivations across an étale chart localization

The canonical base-change isomorphism on Kähler differentials extends a
point derivation and preserves its value on every original regular function.
-/

variable (K R S C : Type*) [CommRing K] [CommRing R] [CommRing S] [CommRing C]
  [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
  [Algebra K C] [Algebra R C] [Algebra S C]
  [IsScalarTower K R C] [IsScalarTower K S C] [IsScalarTower R S C]
  [Algebra.FormallyEtale R S]

/-- Extend a point-valued derivation using the actual étale cotangent
base-change map, in particular for a principal localization. -/
def etaleExtendDerivation (δ : Derivation K R C) : Derivation K S C :=
  KaehlerDifferential.linearMapEquivDerivation K S
    ((δ.liftKaehlerDifferential.liftBaseChange S).comp
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K R S).symm.toLinearMap)

@[simp]
theorem etaleExtendDerivation_algebraMap (δ : Derivation K R C) (r : R) :
    etaleExtendDerivation K R S C δ (algebraMap R S r) = δ r := by
  change δ.liftKaehlerDifferential.liftBaseChange S
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K R S).symm
      (KaehlerDifferential.D K S (algebraMap R S r))) = δ r
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul, one_smul, Derivation.liftKaehlerDifferential_comp_D]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.EtaleDerivation.Constructions
