import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientLiftNaturality
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.EtaleDerivation

/-! # Etale Coefficient Lift Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleCoefficientLiftEquivalence

noncomputable section

/-! Etale restriction gives a coefficient-linear equivalence of
actual dual-number lifts, with no field or local-ring assumption on
the coefficient algebra. -/

variable (k B D C : Type) [CommRing k] [CommRing B] [CommRing D] [CommRing C]
    [Algebra k B] [Algebra k D] [Algebra k C] [Algebra B D] [Algebra B C] [Algebra D C]
    [IsScalarTower k B D] [IsScalarTower k B C] [IsScalarTower k D C] [IsScalarTower B D C]
    [Algebra.FormallyEtale B D]

theorem etaleCoefficientDerivation_ext (d e : Derivation k D C)
    (h : ∀ b : B, d (algebraMap B D b) = e (algebraMap B D b)) : d = e := by
  have hd : d.liftKaehlerDifferential = e.liftKaehlerDifferential := by
    apply (KaehlerDifferential.isBaseChange_of_formallyEtale k B D).algHom_ext'
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro b
    change d.liftKaehlerDifferential
        (KaehlerDifferential.map k k B D (KaehlerDifferential.D k B b)) =
      e.liftKaehlerDifferential
        (KaehlerDifferential.map k k B D (KaehlerDifferential.D k B b))
    rw [KaehlerDifferential.map_D, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D]
    exact h b
  apply Derivation.ext
  intro d'
  rw [← Derivation.liftKaehlerDifferential_comp_D d d',
    ← Derivation.liftKaehlerDifferential_comp_D e d', hd]

theorem coefficientDerivationPrecomposition_bijective :
    Function.Bijective (Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k B D C) := by
  constructor
  · intro d e h
    exact etaleCoefficientDerivation_ext k B D C d e (fun b => Derivation.congr_fun h b)
  · intro d
    refine ⟨HodgeConjecture.DegreeTwo.EtaleDerivation.Constructions.etaleExtendDerivation k B D C d, ?_⟩
    exact Derivation.ext (HodgeConjecture.DegreeTwo.EtaleDerivation.Constructions.etaleExtendDerivation_algebraMap k B D C d)

def coefficientDerivationPrecompositionEquiv : Derivation k D C ≃ₗ[C] Derivation k B C :=
  LinearEquiv.ofBijective (Dual.CoefficientLiftNaturality.coefficientDerivationPrecomposition k B D C)
    (coefficientDerivationPrecomposition_bijective k B D C)

def etaleCoefficientLiftEquiv : Dual.AlgebraLiftCoordinates.DualCoefficientLifts.Space C k D ≃ₗ[C] Dual.AlgebraLiftCoordinates.DualCoefficientLifts.Space C k B :=
  (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv C k D).trans
    ((coefficientDerivationPrecompositionEquiv k B D C).trans (Dual.AlgebraLiftCoordinates.DualCoefficientLifts.derivationEquiv C k B).symm)

theorem etaleCoefficientLiftEquiv_hom (v : Dual.AlgebraLiftCoordinates.DualCoefficientLifts.Space C k D) (b : B) :
    (etaleCoefficientLiftEquiv k B D C v).val.hom b = v.val.hom (algebraMap B D b) :=
  Dual.CoefficientLiftNaturality.dualCoefficientLiftPrecomposition_hom k B D C v b

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleCoefficientLiftEquivalence
