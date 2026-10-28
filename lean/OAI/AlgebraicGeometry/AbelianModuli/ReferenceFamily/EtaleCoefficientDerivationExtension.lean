import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleCoefficientLiftEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientLiftNaturality

/-! # Etale Coefficient Derivation Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleCoefficientDerivationExtension

noncomputable section

/-! Etale extension of coefficient-valued derivations is linear and
commutes with coefficient change, retaining the original values on the
source chart. -/

variable (k A D C : Type) [CommRing k] [CommRing A] [CommRing D] [CommRing C]
    [Algebra k A] [Algebra k D] [Algebra k C] [Algebra A D] [Algebra A C] [Algebra D C]
    [IsScalarTower k A D] [IsScalarTower k A C] [IsScalarTower k D C] [IsScalarTower A D C]
    [Algebra.FormallyEtale A D]

def etaleCoefficientDerivationExtension : Derivation k A C →ₗ[C] Derivation k D C :=
  (EtaleCoefficientLiftEquivalence.coefficientDerivationPrecompositionEquiv k A D C).symm.toLinearMap

theorem etaleCoefficientDerivationExtension_algebraMap (d : Derivation k A C) (a : A) :
    etaleCoefficientDerivationExtension k A D C d (algebraMap A D a) = d a :=
  Derivation.congr_fun ((EtaleCoefficientLiftEquivalence.coefficientDerivationPrecompositionEquiv k A D C).apply_symm_apply d) a

theorem etaleCoefficientDerivationExtension_eq (d : Derivation k A C) :
    etaleCoefficientDerivationExtension k A D C d =
      HodgeConjecture.DegreeTwo.EtaleDerivation.Constructions.etaleExtendDerivation k A D C d := by
  apply EtaleCoefficientLiftEquivalence.etaleCoefficientDerivation_ext k A D C
  intro a
  rw [etaleCoefficientDerivationExtension_algebraMap,
    HodgeConjecture.DegreeTwo.EtaleDerivation.Constructions.etaleExtendDerivation_algebraMap]

variable (C' : Type) [CommRing C'] [Algebra k C'] [Algebra A C'] [Algebra D C']
    [IsScalarTower k A C'] [IsScalarTower k D C'] [IsScalarTower A D C']

theorem etaleCoefficientDerivationExtension_coefficients (q : C →ₐ[D] C') (d : Derivation k A C) :
    Dual.CoefficientLiftNaturality.coefficientDerivationMap k D C C' q (etaleCoefficientDerivationExtension k A D C d) =
      etaleCoefficientDerivationExtension k A D C'
        (Dual.CoefficientLiftNaturality.coefficientDerivationMap k A C C' (q.restrictScalars A) d) := by
  apply EtaleCoefficientLiftEquivalence.etaleCoefficientDerivation_ext k A D C'
  intro a
  change q (etaleCoefficientDerivationExtension k A D C d (algebraMap A D a)) =
    etaleCoefficientDerivationExtension k A D C'
      (Dual.CoefficientLiftNaturality.coefficientDerivationMap k A C C' (q.restrictScalars A) d) (algebraMap A D a)
  rw [etaleCoefficientDerivationExtension_algebraMap, etaleCoefficientDerivationExtension_algebraMap]
  rfl

variable (F : Type) [CommRing F] [Algebra k F] [Algebra A F] [Algebra D F] [Algebra F C]
    [IsScalarTower k A F] [IsScalarTower k D F] [IsScalarTower k F C]
    [IsScalarTower A D F] [IsScalarTower A F C] [IsScalarTower D F C]
    [Algebra.FormallyEtale D F] [Algebra.FormallyEtale A F]

theorem etaleCoefficientDerivationExtension_tower (d : Derivation k A C) :
    etaleCoefficientDerivationExtension k A F C d =
      etaleCoefficientDerivationExtension k D F C (etaleCoefficientDerivationExtension k A D C d) := by
  apply EtaleCoefficientLiftEquivalence.etaleCoefficientDerivation_ext k A F C
  intro a
  rw [etaleCoefficientDerivationExtension_algebraMap, IsScalarTower.algebraMap_apply A D F a,
    etaleCoefficientDerivationExtension_algebraMap, etaleCoefficientDerivationExtension_algebraMap]

variable (R : Type) [CommRing R] [Algebra k R] [Algebra R A] [Algebra R D] [Algebra R C]
    [IsScalarTower k R A] [IsScalarTower k R D] [IsScalarTower k R C]
    [IsScalarTower R A D] [IsScalarTower R A C] [IsScalarTower R D C]

omit [IsScalarTower k R C] in
theorem etaleCoefficientDerivationExtension_base (d : Derivation k A C) :
    (etaleCoefficientDerivationExtension k A D C d).compAlgebraMap R = d.compAlgebraMap R := by
  apply Derivation.ext
  intro r
  change etaleCoefficientDerivationExtension k A D C d (algebraMap R D r) = d (algebraMap R A r)
  rw [IsScalarTower.algebraMap_apply R A D r, etaleCoefficientDerivationExtension_algebraMap]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EtaleCoefficientDerivationExtension
